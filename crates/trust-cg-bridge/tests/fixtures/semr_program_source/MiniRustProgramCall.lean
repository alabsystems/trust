/- Complete actual Call-constructor operation, factored mechanically at six
   primitive constants. actual_call checks the original instantiation by rfl.
   All preparation, argument, call, error and world paths remain unchanged. -/
import MiniRust
set_option autoImplicit false
noncomputable section
namespace MiniRustProgramCall

def callWith
    (evalPlace : Nat → MR_Machine → MR_PlaceExpr →
      SOut (SRes MR_TerminationInfo (MR_Place × MR_Type) × MR_Machine))
    (prepare : Nat → MR_Machine → MR_Place → MR_Type →
      SOut (SRes MR_TerminationInfo Unit × MR_Machine))
    (evalValue : Nat → MR_Machine → MR_ValueExpr →
      SOut (SRes MR_TerminationInfo (MR_Value × MR_Type) × MR_Machine))
    (lookup : Nat → MR_Machine → MR_Value → SOut (SRes MR_TerminationInfo MR_Function))
    (evalArgument : Nat → MR_Machine → MR_ArgumentExpr →
      SOut (SRes MR_TerminationInfo (MR_Value × MR_Type) × MR_Machine))
    (evalCall : Nat → MR_Machine → MR_Function → MR_CallingConvention →
      List (MR_Value × MR_Type) → (MR_Place × MR_Type) → Option MR_BbName → Option MR_BbName →
      SOut (SRes MR_TerminationInfo Unit × MR_Machine))
    (fuel : Nat) (self_5993 : MR_Machine) (f_6026 : MR_ValueExpr)
    (f_6027 : MR_CallingConvention) (f_6028 : List MR_ArgumentExpr)
    (f_6029 : MR_PlaceExpr) (f_6030 f_6031 : Option MR_BbName) :
    SOut (SRes MR_TerminationInfo Unit × MR_Machine) :=
  match fuel with
  | 0 => .fuel
  | fuel + 1 =>
    let jp_5995 : SRes MR_TerminationInfo Unit → MR_Machine →
        SOut (SRes MR_TerminationInfo Unit × MR_Machine) :=
      fun result machine => .ok (result, machine)
    SOut.bind (α := (SRes MR_TerminationInfo (MR_Place × MR_Type) × MR_Machine)) (β := (SRes MR_TerminationInfo Unit × MR_Machine)) (evalPlace fuel self_5993 f_6029) (fun (p_6034 : SRes MR_TerminationInfo (MR_Place × MR_Type) × MR_Machine) => match p_6034 with | (r_6032, r_6033) => let self_6035 : MR_Machine := r_6033; (match r_6032 with | SRes.ok ok_6036 => (match ok_6036 with | (c_6038, c_6039) => SOut.bind (α := (SRes MR_TerminationInfo Unit × MR_Machine)) (β := (SRes MR_TerminationInfo Unit × MR_Machine)) (prepare fuel self_6035 c_6038 c_6039) (fun (p_6042 : SRes MR_TerminationInfo Unit × MR_Machine) => match p_6042 with | (r_6040, r_6041) => let self_6043 : MR_Machine := r_6041; (match r_6040 with | SRes.ok ok_6044 => SOut.bind (α := (SRes MR_TerminationInfo (MR_Value × MR_Type) × MR_Machine)) (β := (SRes MR_TerminationInfo Unit × MR_Machine)) (evalValue fuel self_6043 f_6026) (fun (p_6048 : SRes MR_TerminationInfo (MR_Value × MR_Type) × MR_Machine) => match p_6048 with | (r_6046, r_6047) => let self_6049 : MR_Machine := r_6047; (match r_6046 with | SRes.ok ok_6050 => (match ok_6050 with | (c_6052, c_6053) => SOut.bind (α := (SRes MR_TerminationInfo MR_Function)) (β := (SRes MR_TerminationInfo Unit × MR_Machine)) (lookup fuel self_6049 c_6052) (fun (r_6054 : SRes MR_TerminationInfo MR_Function) => (match r_6054 with | SRes.ok ok_6055 => SOut.bind (α := (SRes MR_TerminationInfo (List (MR_Value × MR_Type)) × MR_Machine)) (β := (SRes MR_TerminationInfo Unit × MR_Machine)) (SList.tryMapResS (α := MR_ArgumentExpr) (β := (MR_Value × MR_Type)) (ε := MR_TerminationInfo) (σ := MR_Machine) f_6028 (fun (a_6069 : MR_ArgumentExpr) (st_6075 : MR_Machine) => match st_6075 with | self_6070 => SOut.bind (α := (SRes MR_TerminationInfo (MR_Value × MR_Type) × MR_Machine)) (β := (SRes MR_TerminationInfo (MR_Value × MR_Type) × MR_Machine)) (evalArgument fuel self_6070 a_6069) (fun (p_6073 : SRes MR_TerminationInfo (MR_Value × MR_Type) × MR_Machine) => match p_6073 with | (r_6071, r_6072) => let self_6074 : MR_Machine := r_6072; SOut.ok (r_6071, self_6074))) self_6049) (fun (p_6078 : SRes MR_TerminationInfo (List (MR_Value × MR_Type)) × MR_Machine) => match p_6078 with | (r_6076, r_6077) => let w_6079 := r_6077; let self_6080 : MR_Machine := w_6079; (match r_6076 with | SRes.ok ok_6081 => SOut.bind (α := (SRes MR_TerminationInfo Unit × MR_Machine)) (β := (SRes MR_TerminationInfo Unit × MR_Machine)) (evalCall fuel self_6080 ok_6055 f_6027 ok_6081 (c_6038, c_6039) f_6030 f_6031) (fun (p_6085 : SRes MR_TerminationInfo Unit × MR_Machine) => match p_6085 with | (r_6083, r_6084) => let self_6086 : MR_Machine := r_6084; jp_5995 r_6083 self_6086) | SRes.err err_6082 => SOut.ok ((SRes.err err_6082 : SRes MR_TerminationInfo Unit), self_6080))) | SRes.err err_6056 => SOut.ok ((SRes.err err_6056 : SRes MR_TerminationInfo Unit), self_6049)))) | SRes.err err_6051 => SOut.ok ((SRes.err err_6051 : SRes MR_TerminationInfo Unit), self_6049))) | SRes.err err_6045 => SOut.ok ((SRes.err err_6045 : SRes MR_TerminationInfo Unit), self_6043)))) | SRes.err err_6037 => SOut.ok ((SRes.err err_6037 : SRes MR_TerminationInfo Unit), self_6035)))

theorem actual_call (fuel : Nat) (machine : MR_Machine) (target : MR_ValueExpr)
    (cc : MR_CallingConvention) (args : List MR_ArgumentExpr) (ret : MR_PlaceExpr)
    (next unwind : Option MR_BbName) :
    MRf.Machine.eval_terminator fuel machine (.Call target cc args ret next unwind) =
      callWith MRf.Machine.eval_place MRf.Machine.prepare_for_inplace_passing
        MRf.Machine.eval_value MRf.Machine.fn_from_ptr MRf.Machine.eval_argument
        MRf.Machine.eval_call fuel machine target cc args ret next unwind := by
  cases fuel <;> rfl

end MiniRustProgramCall
