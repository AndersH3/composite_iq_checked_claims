package body Towers_Boundary_Models with SPARK_Mode is
   procedure Project_Conditional
     (J, M, Old_J, Old_M : Long_Long_Integer) is
   begin
      null;
   end Project_Conditional;

   procedure Project_Grid_Cell (Total, Joint, Marginal : Long_Float) is
   begin
      null;
   end Project_Grid_Cell;

   procedure Observe_Sqrt (X, Y : Long_Float) is begin null; end Observe_Sqrt;
   procedure Observe_Survival (Z, P : Long_Float) is begin null; end Observe_Survival;
   procedure Observe_Log (X, Y : Long_Float) is begin null; end Observe_Log;
   procedure Observe_Exp (X, Y : Long_Float) is begin null; end Observe_Exp;
   procedure Observe_Trig (Value : Long_Float) is begin null; end Observe_Trig;
   procedure Observe_Exponent (Before, After : Long_Float) is begin null; end Observe_Exponent;
   procedure Observe_Probability (Before, After : Long_Float) is begin null; end Observe_Probability;
   procedure Observe_Node (Before, After : Long_Float) is begin null; end Observe_Node;
   procedure Observe_Grid_Cell
     (Total, Joint, Marginal, Old_Total, Old_Joint, Old_Marginal : Long_Float) is
   begin null; end Observe_Grid_Cell;
   procedure Observe_Quantization
     (P : Long_Float; Before, After : Long_Long_Integer) is
   begin null; end Observe_Quantization;
   procedure Observe_Union (A, B, J, Old_A, Old_B, Old_J : Long_Long_Integer) is
   begin null; end Observe_Union;
   procedure Observe_Conditional (J, M, Old_J, Old_M : Long_Long_Integer) is
   begin null; end Observe_Conditional;
   procedure Observe_Joint (J, A, B, Old_J : Long_Float) is
   begin null; end Observe_Joint;
   procedure Observe_Inverse_Bracket (P, Lower_Tail, Upper_Tail : Long_Float) is
   begin null; end Observe_Inverse_Bracket;
end Towers_Boundary_Models;
