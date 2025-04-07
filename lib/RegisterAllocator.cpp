#include <llvm/Analysis/AliasAnalysis.h>
#include <llvm/CodeGen/LiveIntervals.h>
#include <llvm/CodeGen/LiveRangeEdit.h>
#include <llvm/CodeGen/LiveRegMatrix.h>
#include <llvm/CodeGen/LiveStacks.h>
#include <llvm/CodeGen/MachineBlockFrequencyInfo.h>
#include <llvm/CodeGen/MachineDominators.h>
#include <llvm/CodeGen/MachineFunctionPass.h>
#include <llvm/CodeGen/MachineLoopInfo.h>
#include <llvm/CodeGen/RegAllocRegistry.h>
#include <llvm/CodeGen/RegisterClassInfo.h>
#include <llvm/CodeGen/Spiller.h>
#include <llvm/CodeGen/VirtRegMap.h>
#include <llvm/InitializePasses.h>
#include <llvm/Support/raw_ostream.h>

#include "queue"

using namespace llvm;

namespace {

class RegisterAllocatorMinimal: public MachineFunctionPass {
private:
    MachineFunction *MF;
    /*
    Each Machine Instruction has a unique ID. This is useful for defining the
    live range of a Virtual Register
    */
    const SlotIndexes *SI;

    /*
    Records the Valid Assignment of the Virtual Register to a Physical register.
    If spilling is required, VirtRegMap coordinates stack slot allocation
    */
    VirtRegMap *VRM;

    /*
    Physical Register information of the Target Architecture
    */
    const TargetRegisterInfo *TRI;

    /*
    "Machine Register Info" or "Machine Register Interface", contains information about Virtual Registers
    */
    MachineRegisterInfo *MRI;

    // Live Intervals
    LiveIntervals *LIS;
    
    // LiveIntervalQueue: Keeps track of the Valid LiveIntervals which needs assignment.
    std::queue<LiveInterval *> LIQ;

    // Add LiveInterval LI to Queue
    void enqueue(LiveInterval *const LI) {
        outs() << "Adding {Register=" << *LI << "}\n";
        LIQ.push(LI);
    }

    // Remove LiveInterval LI from the Queue in FIFO manner.
    LiveInterval* dequeue() {
        if(LIQ.empty()) {
            return nullptr;
        }
        LiveInterval* LI = LIQ.front();
        outs() << "Popping {Reg=" << *LI << "}\n";
        LIQ.pop();

        return LI;
    }

    /*
    The LiveRegMatrix class in LLVM tracks virtual register interference along two dimensions: slot indexes and register units.
    
    Contains information about the Interferences. This is similar to Interference Graph.
    
    The "smallest units of interference" in the context of register allocation refers to register units, which represent 
    the most granular level at which registers can interfere with each other.

    For example:
        1. In x86, there are overlapping registers of different sizes, such as:
            - AL (8-bit)
            - AX (16-bit, contains AL)
            - EAX (32-bit, contains AX)
            - RAX (64-bit, contains EAX)
        2. Register units for these might look like:
            - AL: Unit 1
            - AH: Unit 2
            .
            .
        In this example, if a virtual register is assigned to AL, it would interfere with any other virtual register assigned to AL, AX, EAX, or RAX, but not with AH.
    */
    LiveRegMatrix *LRM;

    // Register Class Information
    RegisterClassInfo RCI;

    // Spiller
    std::unique_ptr<Spiller> SpillerInst;


public:
    static char ID;

    StringRef getPassName() const override {
        return "Minimal Register Allocator";
    }

    RegisterAllocatorMinimal() : MachineFunctionPass(ID) {}

    /*
    Get the requried analysis passes
    */
    void getAnalysisUsage(AnalysisUsage &AU) const override {
        MachineFunctionPass::getAnalysisUsage(AU);
        AU.setPreservesCFG();

#define REQUIRE_AND_PRESERVE_PASS(PassName)                                    \
  AU.addRequired<PassName>();                                                  \
  AU.addPreserved<PassName>()

        REQUIRE_AND_PRESERVE_PASS(SlotIndexes);
        REQUIRE_AND_PRESERVE_PASS(VirtRegMap);
        REQUIRE_AND_PRESERVE_PASS(LiveIntervals);
        REQUIRE_AND_PRESERVE_PASS(LiveRegMatrix);

        // implicitly requested by the spiller
        REQUIRE_AND_PRESERVE_PASS(LiveStacks);
        REQUIRE_AND_PRESERVE_PASS(AAResultsWrapperPass);
        REQUIRE_AND_PRESERVE_PASS(MachineDominatorTree);
        REQUIRE_AND_PRESERVE_PASS(MachineLoopInfo);
        REQUIRE_AND_PRESERVE_PASS(MachineBlockFrequencyInfo);
    }

    /*
    Request PHI Nodes are removed before doing Register Allocation
    */
    MachineFunctionProperties getRequiredProperties() const override {
        return MachineFunctionProperties().set(
            MachineFunctionProperties::Property::NoPHIs
        );
    }

    /*
    Specifies which properties should be cleared after the pass has executed 
    because they are no longer valid.
    */
    MachineFunctionProperties getClearedProperties() const override {
        // No longer in SSA format because we removed the PHI Nodes, and we will be allocating actual registers.
        return MachineFunctionProperties().set(
            MachineFunctionProperties::Property::IsSSA
        );
    }

    bool runOnMachineFunction(MachineFunction &MF) override {
        this->MF = &MF;

        outs() << "************************************************\n"
               << "* Machine Function\n"
               << "************************************************\n";
        
        // 0. Get all the Analysis from the Passes

        // Get Analysis from SlotIndex Pass
        SI = &getAnalysis<SlotIndexes>();

        for (const MachineBasicBlock &MBB: MF) {
            MBB.print(outs(), SI);
            outs() << "\n";
        }
        outs() << "\n\n";
        /* 
        Get Analysis from the 
            VirtRegMap 
            LiveIntervals and,
            LiveRegMatrix passes.
        */
        // The *VirtRegMap* maps virtual registers to physical registers and
        // virtual registers to stack slots.
        VRM = &getAnalysis<VirtRegMap>();
        TRI = &VRM->getTargetRegInfo();
        MRI = &VRM->getRegInfo();

        /*
        Some physical registers of the architecture that are reserved for some operations 
        like parameter passing, return values and others.

        freezeReservedRegs method of the MachineRegisterInfo method will make the reserved 
        physical register unaccessible during register allocation.
        */
        MRI->freezeReservedRegs();
        LIS = &getAnalysis<LiveIntervals>();
        LRM = &getAnalysis<LiveRegMatrix>();
    
        // The *RegisterClassInfo* provides dynamic information about target
        // register classes. We will be leveraging it to obtain a plausible
        // allocation order of physical registers.
        RCI.runOnMachineFunction(MF);


        // 1. Get Valid Virtual Registers and enqueue them
        for(unsigned virtualRegIdx = 0; virtualRegIdx < MRI->getNumVirtRegs(); virtualRegIdx++) {
            Register Reg = Register::index2VirtReg(virtualRegIdx);

            /*
            Return true if the only instructions using or defining Reg are Debug instructions. 
            (No non-debug instruction is usign this Reg)
            */
            if(MRI->reg_nodbg_empty(Reg)) {
                continue;
            }
            
            enqueue(&LIS->getInterval(Reg));
        }


        return false;
    }


};

char RegisterAllocatorMinimal::ID = 0;

/* 
Register a new Register Allocator.

LLVM Backend Passes still rely on the Legacy Pass Managers.

Parameters
    "register-allocator-minimal": 
        The command-line name of the register allocator.
        Users can select this allocator using -regalloc=minimal.

    "Minimal Register Allocator":
        A descriptive string for the allocator.

    Lambda Function ([]() -> FunctionPass *):
        A factory function that creates an instance of the custom register allocator (RegisterAllocatorMinimal).
        The lambda returns a pointer to a FunctionPass, which is the base class for LLVM's backend passes.
*/
static RegisterRegAlloc X("register-allocator-minimal", "Minimal Register Allocator", 
[]() -> FunctionPass* {return new RegisterAllocatorMinimal();});
}

