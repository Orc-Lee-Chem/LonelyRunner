import LonelyRunnerNew.Inputs
import LonelyRunnerNew.CertificateData

/- Target propositions. Conditional and unconditional main theorems are not yet proved. -/
namespace LonelyRunnerNew
def separatedTarget : Prop :=
  roughBlockInput → kernelInput → separatedControl (Real.exp 6880) (17/100)
def conditionalTarget : Prop :=
  roughBlockInput → kernelInput → spilloverInput → forestInput → mainStatement
def rationalEndgameTarget : Prop :=
  (4*Certificate.Cbar)^50 * Certificate.Bbar^201 <
    (Certificate.wbar*Certificate.tbar)^201

/- Planned declarations after actual proofs are written:
theorem separated_control (hA : roughBlockInput) (hB : kernelInput) :
    separatedControl (Real.exp 6880) (17/100) := ...
theorem conditional_main (hA : roughBlockInput) (hB : kernelInput)
    (hS : spilloverInput) (hF : forestInput) : mainStatement := ...
theorem main_unconditional : mainStatement := ...

The last theorem is allowed only after all four inputs are proved.
Audit the complete types as well as #print axioms.
-/
end LonelyRunnerNew
