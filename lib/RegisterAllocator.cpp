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

namespace llvm {

void initializeRegisterAllocatorMinimalPass(PassRegistry &Registry);

}

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

        REQUIRE_AND_PRESERVE_PASS(SlotIndexesWrapperPass);
        REQUIRE_AND_PRESERVE_PASS(VirtRegMap);
        REQUIRE_AND_PRESERVE_PASS(LiveIntervalsWrapperPass);
        REQUIRE_AND_PRESERVE_PASS(LiveRegMatrix);

        // implicitly requested by the spiller
        REQUIRE_AND_PRESERVE_PASS(LiveStacks);
        REQUIRE_AND_PRESERVE_PASS(AAResultsWrapperPass);
        REQUIRE_AND_PRESERVE_PASS(MachineDominatorTreeWrapperPass);
        REQUIRE_AND_PRESERVE_PASS(MachineLoopInfoWrapperPass);
        REQUIRE_AND_PRESERVE_PASS(MachineBlockFrequencyInfoWrapperPass);
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
    Either assign a Physical Register to the Live Interval or split into mutliple Live Interval.
    */
    MCRegister selectOrSplit(LiveInterval *const LI, SmallVectorImpl<Register> *const SplitVirtRegs) {
        /*
        2.1 Obtain the Plausible Allocation Order
        Allocation Order captures the preferred allocation order for a virtual register
        */

        ArrayRef<MCPhysReg> Order = RCI.getOrder(MF->getRegInfo().getRegClass(LI->reg()));
        SmallVector<MCPhysReg, 16> Hints;

        /*
        1. AllocationHints:
            - Provide suggestions for preferred physical registers for a given virtual register.
            - Generated by the target-specific code or based on certain heuristics.
            - Used as input to create an AllocationOrder.

        2. AllocationOrder:
            - Encapsulates the preferred allocation order for a virtual register.
            - Takes into account both allocation hints and the target's register "default" allocation order.

        The AllocationOrder class in LLVM takes into account both the current allocation order and allocation hints
        to create an optimized sequence of physical registers for allocation.

        */
        bool IsHardHint = TRI->getRegAllocationHints(LI->reg(), Order, Hints, *MF, VRM, LRM);
        /*
        Get a list of 'hint' registers that the register allocator should try first when allocating a physical register for the virtual register VirtReg.
        These registers are effectively moved to the front of the allocation order.
        If true is returned, regalloc will try to only use hints to the greatest extent possible even if it means spilling.
        If not, we will consider registe from Allocation order as well.
        */
        if (!IsHardHint) {
            for (const MCPhysReg &PhysReg : Order) {
                Hints.push_back(PhysReg);
            }
        }

        outs() << "Hint Registers: [";
        for (const MCPhysReg &PhysReg : Hints) {
            outs() << TRI->getRegAsmName(PhysReg) << ", ";
            }
        outs() << "]\n";

        // Spill Candidates
        SmallVector<MCRegister, 8> PhysRegSpillCandidates;
        for(MCRegister PhyReg: Hints) {
            // 2.2 Check for interference
            switch(LRM->checkInterference(*LI, PhyReg)) {
                case LiveRegMatrix::IK_Free:
                // Allocate the first non-infereing (available) register
                outs() << "Assigning the Physical register: " << TRI->getRegAsmName(PhyReg) << "\n";
                return PhyReg;

                case LiveRegMatrix::IK_VirtReg:
                // Interfereing with another VirtReg which has been assigned this PhysReg
                // Possible Spill Candidate?
                PhysRegSpillCandidates.push_back(PhyReg);
                continue;
                default:
                // We also have possible interference with the RegUnit & Reserver ones, we just continue
                continue;
            }
        }

        // 2.3. Attempt to spill another interfering reg with less spill weight.
        for(MCRegister PhysReg: PhysRegSpillCandidates) {
            // TODO: Spill Virtual Register
            outs() << TRI->getRegAsmName(PhysReg);
        }

        // TODO: 2.4 Notify the Caller that the virtual register has been spilled.

        return 0;
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
        SI = &getAnalysis<SlotIndexesWrapperPass>().getSI();

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

            The *VirtRegMap* maps virtual registers to physical registers and
            virtual registers to stack slots.
        */
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
        LIS = &getAnalysis<LiveIntervalsWrapperPass>().getLIS();
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


        while(LiveInterval *const LI = dequeue()) {
            // Check again the VirtReg is used in non-debug instructions also, else just continue
            if(MRI->reg_nodbg_empty(LI->reg())) {
                LIS->removeInterval(LI->reg());
                continue;
            }

            /*
            invalidate cached interference information, we need to obtain the interference info again
            When the live ranges of virtual registers are modified (e.g., due to spilling, coalescing, or splitting), 
            the cached interference information in the LiveRegMatrix becomes stale.
            */
            LRM->invalidateVirtRegs();

            // 2. Assign Physical Register to the Virtual Registers, if not split/spill to a list of Virtual Registers
            SmallVector<Register, 4> SplitVirtualRegister;
            MCRegister PhysReg = selectOrSplit(LI, &SplitVirtualRegister);

            // Assign the Register
            if(PhysReg) {
                LRM->assign(*LI, PhysReg);
            }
        }

        return false;
    }
};

char RegisterAllocatorMinimal::ID = 0;

/* 
Register a new Register Allocator in the LLVM Backend.

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
    
llc -regalloc=register-allocator-minimal input.bc

Note: This just register the customer register allocator
*/
static RegisterRegAlloc X("register-allocator-minimal", "Minimal Register Allocator", 
[]() -> FunctionPass* {return new RegisterAllocatorMinimal();});
}

/*
Ensures that all required analyses (e.g., SlotIndexes, LiveIntervals) are initialized before your allocator runs.
*/

INITIALIZE_PASS_BEGIN(RegisterAllocatorMinimal, "regallominimal", "Minimal Register Allocator",
                      false, false)
INITIALIZE_PASS_DEPENDENCY(SlotIndexesWrapperPass)
INITIALIZE_PASS_DEPENDENCY(VirtRegMap)
INITIALIZE_PASS_DEPENDENCY(LiveIntervalsWrapperPass)
INITIALIZE_PASS_DEPENDENCY(LiveRegMatrix)
INITIALIZE_PASS_DEPENDENCY(LiveStacks);
INITIALIZE_PASS_DEPENDENCY(AAResultsWrapperPass);
INITIALIZE_PASS_DEPENDENCY(MachineDominatorTreeWrapperPass);
INITIALIZE_PASS_DEPENDENCY(MachineLoopInfoWrapperPass);
INITIALIZE_PASS_DEPENDENCY(MachineBlockFrequencyInfoWrapperPass);

INITIALIZE_PASS_END(RegisterAllocatorMinimal, "regallominimal", "Minimal Register Allocator",
                    false, false)

