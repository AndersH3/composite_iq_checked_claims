--  Ordinary pure contracts plus explicit Ghost boundary observations.
--  These predicates describe accepted normal returns. They do not assert
--  transcendental accuracy or prove an off-mode implementation refines them.
package Towers_Boundary_Models with SPARK_Mode is
   Scale : constant Long_Long_Integer := 1_000_000_000_000_000;

   function Sqrt_Normal_Return (X, Y : Long_Float) return Boolean
   is (Y in 0.0 .. 1.0E3
       and then (if X >= 1.0E-30 then Y >= 1.0E-15)
       and then (if X >= 0.0625 then Y >= 0.25)
       and then (if X >= 1.0 then Y >= 1.0)
       and then (if X <= 1.0 then Y <= 1.0)
       and then (if X <= 4.0 then Y <= 2.0)
       and then (if X <= 64.0 then Y <= 8.0)) with
     Post => (if Sqrt_Normal_Return'Result then Y in 0.0 .. 1.0E3) and then
       (if Sqrt_Normal_Return'Result then (if X >= 1.0E-30 then Y >= 1.0E-15) and then (if X >= 0.0625 then Y >= 0.25) and then (if X >= 1.0 then Y >= 1.0) and then (if X <= 1.0 then Y <= 1.0) and then (if X <= 4.0 then Y <= 2.0) and then (if X <= 64.0 then Y <= 8.0)) and then
       (if Y in 0.0 .. 1.0E3
       and then (if X >= 1.0E-30 then Y >= 1.0E-15)
       and then (if X >= 0.0625 then Y >= 0.25)
       and then (if X >= 1.0 then Y >= 1.0)
       and then (if X <= 1.0 then Y <= 1.0)
       and then (if X <= 4.0 then Y <= 2.0)
       and then (if X <= 64.0 then Y <= 8.0) then Sqrt_Normal_Return'Result),
     Global => null,
     Depends => (Sqrt_Normal_Return'Result => (X, Y));

   function Survival_Normal_Return (Z, P : Long_Float) return Boolean
   is (P in 0.0 .. 1.0
       and then (if Z >= 10.0 then P < 1.0E-20)
       and then (if Z <= -10.0 then P > 1.0 - 1.0E-14)) with
     Post => (if Survival_Normal_Return'Result then P in 0.0 .. 1.0) and then
       (if Survival_Normal_Return'Result then (if Z >= 10.0 then P < 1.0E-20) and then (if Z <= -10.0 then P > 1.0 - 1.0E-14)) and then
       (if P in 0.0 .. 1.0
       and then (if Z >= 10.0 then P < 1.0E-20)
       and then (if Z <= -10.0 then P > 1.0 - 1.0E-14) then Survival_Normal_Return'Result),
     Global => null,
     Depends => (Survival_Normal_Return'Result => (Z, P));

   function Log_Normal_Return (X, Y : Long_Float) return Boolean
   is (X in 4.0E-10 .. 0.9999999999 and then Y in -23.0 .. 0.0) with
     Post => (if Log_Normal_Return'Result then X in 4.0E-10 .. 0.9999999999) and then
       (if Log_Normal_Return'Result then Y in -23.0 .. 0.0) and then
       (if X in 4.0E-10 .. 0.9999999999 and then Y in -23.0 .. 0.0 then Log_Normal_Return'Result),
     Global => null,
     Depends => (Log_Normal_Return'Result => (X, Y));

   function Exp_Normal_Return (X, Y : Long_Float) return Boolean
   is (X <= 1.0E-9 and then Y in 0.0 .. 1.0001) with
     Post => (if Exp_Normal_Return'Result then X <= 1.0E-9) and then
       (if Exp_Normal_Return'Result then Y in 0.0 .. 1.0001) and then
       (if X <= 1.0E-9 and then Y in 0.0 .. 1.0001 then Exp_Normal_Return'Result),
     Global => null,
     Depends => (Exp_Normal_Return'Result => (X, Y));

   --  Range abstraction of an observed Sin/Cos value. The installed Ada
   --  specifications supply this bound; the backend and accuracy are unproved.
   function Trigonometric_Value (Value : Long_Float) return Boolean
   is (Value in -1.0 .. 1.0) with
     Post => (if Trigonometric_Value'Result then Value >= -1.0) and then
       (if Trigonometric_Value'Result then Value <= 1.0) and then
       (if Value in -1.0 .. 1.0 then Trigonometric_Value'Result),
     Global => null,
     Depends => (Trigonometric_Value'Result => Value);

   function Exponent_Normal_Return (Before, After : Long_Float) return Boolean
   is (After = Before and then After <= 1.0E-9) with
     Post => (if Exponent_Normal_Return'Result then After = Before) and then
       (if Exponent_Normal_Return'Result then After <= 1.0E-9) and then
       (if After = Before and then After <= 1.0E-9 then Exponent_Normal_Return'Result),
     Global => null,
     Depends => (Exponent_Normal_Return'Result => (Before, After));

   function Probability_Normal_Return (Before, After : Long_Float) return Boolean
   is (After = Before and then After in 0.0 .. 1.0) with
     Post => (if Probability_Normal_Return'Result then After = Before) and then
       (if Probability_Normal_Return'Result then After in 0.0 .. 1.0) and then
       (if After = Before and then After in 0.0 .. 1.0 then Probability_Normal_Return'Result),
     Global => null,
     Depends => (Probability_Normal_Return'Result => (Before, After));

   function Node_Normal_Return (Before, After : Long_Float) return Boolean
   is (After = Before and then After in 0.0 .. 0.96) with
     Post => (if Node_Normal_Return'Result then After = Before) and then
       (if Node_Normal_Return'Result then After in 0.0 .. 0.96) and then
       (if After = Before and then After in 0.0 .. 0.96 then Node_Normal_Return'Result),
     Global => null,
     Depends => (Node_Normal_Return'Result => (Before, After));

   function Grid_Cell_Normal_Return
     (Total, Joint, Marginal : Long_Float) return Boolean
   is (Total in 1.0E-100 .. 1.0E6 and then
       Joint in 0.0 .. Total and then Marginal in 0.0 .. Total) with
     Post => (if Grid_Cell_Normal_Return'Result then Total in 1.0E-100 .. 1.0E6) and then
       (if Grid_Cell_Normal_Return'Result then Joint in 0.0 .. Total and then Marginal in 0.0 .. Total) and then
       (if Total in 1.0E-100 .. 1.0E6 and then
       Joint in 0.0 .. Total and then Marginal in 0.0 .. Total then Grid_Cell_Normal_Return'Result),
     Global => null,
     Depends => (Grid_Cell_Normal_Return'Result => (Total, Joint, Marginal));

   function Quantization_Normal_Return
     (P : Long_Float; Before, After : Long_Long_Integer) return Boolean
   is (P in 0.0 .. 1.0 and then Before in 0 .. Scale
       and then After = Before and then
       abs (Long_Float (After) / Long_Float (Scale) - P) <= 0.51E-15) with
     Post => (if Quantization_Normal_Return'Result then P in 0.0 .. 1.0) and then
       (if Quantization_Normal_Return'Result then Before in 0 .. Scale and then After = Before and then abs (Long_Float (After) / Long_Float (Scale) - P) <= 0.51E-15) and then
       (if P in 0.0 .. 1.0 and then Before in 0 .. Scale
       and then After = Before and then
       abs (Long_Float (After) / Long_Float (Scale) - P) <= 0.51E-15 then Quantization_Normal_Return'Result),
     Global => null,
     Depends => (Quantization_Normal_Return'Result => (P, Before, After));

   function Union_Normal_Return
     (A, B, J, Old_A, Old_B, Old_J : Long_Long_Integer) return Boolean
   is (A in 0 .. Scale and then B in 0 .. Scale and then J in 0 .. Scale
       and then A = Old_A and then B = Old_B and then J = Old_J
       and then J <= A and then J <= B and then A + B <= Scale) with
     Post => (if Union_Normal_Return'Result then A in 0 .. Scale) and then
       (if Union_Normal_Return'Result then B in 0 .. Scale and then J in 0 .. Scale and then A = Old_A and then B = Old_B and then J = Old_J and then J <= A and then J <= B and then A + B <= Scale) and then
       (if A in 0 .. Scale and then B in 0 .. Scale and then J in 0 .. Scale
       and then A = Old_A and then B = Old_B and then J = Old_J
       and then J <= A and then J <= B and then A + B <= Scale then Union_Normal_Return'Result),
     Global => null,
     Depends => (Union_Normal_Return'Result => (A, B, J, Old_A, Old_B, Old_J));

   function Conditional_Normal_Return
     (J, M, Old_J, Old_M : Long_Long_Integer) return Boolean
   is (J in 0 .. Scale and then M in 1 .. Scale
       and then J = Old_J and then M = Old_M and then J <= M) with
     Post => (if Conditional_Normal_Return'Result then J in 0 .. Scale) and then
       (if Conditional_Normal_Return'Result then M in 1 .. Scale and then J = Old_J and then M = Old_M and then J <= M) and then
       (if J in 0 .. Scale and then M in 1 .. Scale
       and then J = Old_J and then M = Old_M and then J <= M then Conditional_Normal_Return'Result),
     Global => null,
     Depends => (Conditional_Normal_Return'Result => (J, M, Old_J, Old_M));

   function Joint_Normal_Return (J, A, B, Old_J : Long_Float) return Boolean
   is (A in 0.0 .. 1.0 and then B in 0.0 .. 1.0
       and then J = Old_J and then J in 0.0 .. A and then J <= B) with
     Post => (if Joint_Normal_Return'Result then A in 0.0 .. 1.0) and then
       (if Joint_Normal_Return'Result then B in 0.0 .. 1.0 and then J = Old_J and then J in 0.0 .. A and then J <= B) and then
       (if A in 0.0 .. 1.0 and then B in 0.0 .. 1.0
       and then J = Old_J and then J in 0.0 .. A and then J <= B then Joint_Normal_Return'Result),
     Global => null,
     Depends => (Joint_Normal_Return'Result => (J, A, B, Old_J));

   --  A proved projection theorem about the model; it does not establish
   --  that erfc, integration, or a guard can never reject at runtime.
   procedure Project_Conditional
     (J, M, Old_J, Old_M : Long_Long_Integer) with
     Global => null,
     Pre => Conditional_Normal_Return (J, M, Old_J, Old_M),
     Post => M > 0 and J >= 0 and J <= M and J = Old_J and M = Old_M,
     Depends => (null => (J, M, Old_J, Old_M)),
     Ghost;

   procedure Project_Grid_Cell (Total, Joint, Marginal : Long_Float) with Ghost,
     Global => null,
     Pre => Grid_Cell_Normal_Return (Total, Joint, Marginal),
     Post => Total > 0.0 and Joint >= 0.0 and Joint <= Total
       and Marginal >= 0.0 and Marginal <= Total,
     Depends => (null => (Total, Joint, Marginal));

   --  Calls in off-mode bodies check model coupling when Ghost is enabled.
   --  Their ghost-only preconditions are erased under Ghost=>Ignore while
   --  every original ordinary Post and concrete guard remains enabled.
   procedure Observe_Sqrt (X, Y : Long_Float) with
     Ghost,
     Global => null,
     Pre => Sqrt_Normal_Return (X, Y),
     Post => Y >= 0.0 and then Y <= 1.0E3,
     Depends => (null => (X, Y));
   procedure Observe_Survival (Z, P : Long_Float) with
     Ghost,
     Global => null,
     Pre => Survival_Normal_Return (Z, P),
     Post => P >= 0.0 and then P <= 1.0,
     Depends => (null => (Z, P));
   procedure Observe_Log (X, Y : Long_Float) with
     Ghost,
     Global => null,
     Pre => Log_Normal_Return (X, Y),
     Post => Y >= -23.0 and then Y <= 0.0,
     Depends => (null => (X, Y));
   procedure Observe_Exp (X, Y : Long_Float) with
     Ghost,
     Global => null,
     Pre => Exp_Normal_Return (X, Y),
     Post => Y >= 0.0 and then Y <= 1.0001,
     Depends => (null => (X, Y));
   procedure Observe_Trig (Value : Long_Float) with
     Ghost,
     Global => null,
     Pre => Trigonometric_Value (Value),
     Post => Value >= -1.0 and then Value <= 1.0,
     Depends => (null => Value);
   procedure Observe_Exponent (Before, After : Long_Float) with
     Ghost,
     Global => null,
     Pre => Exponent_Normal_Return (Before, After),
     Post => After = Before and then After <= 1.0E-9,
     Depends => (null => (Before, After));
   procedure Observe_Probability (Before, After : Long_Float) with
     Ghost,
     Global => null,
     Pre => Probability_Normal_Return (Before, After),
     Post => After = Before and then After in 0.0 .. 1.0,
     Depends => (null => (Before, After));
   procedure Observe_Node (Before, After : Long_Float) with
     Ghost,
     Global => null,
     Pre => Node_Normal_Return (Before, After),
     Post => After = Before and then After in 0.0 .. 0.96,
     Depends => (null => (Before, After));
   procedure Observe_Grid_Cell
     (Total, Joint, Marginal, Old_Total, Old_Joint, Old_Marginal : Long_Float) with Ghost,
     Global => null,
     Pre => Grid_Cell_Normal_Return (Total, Joint, Marginal)
       and Total = Old_Total and Joint = Old_Joint and Marginal = Old_Marginal,
     Post => Total = Old_Total and then Joint = Old_Joint and then Marginal = Old_Marginal,
     Depends => (null => (Total, Joint, Marginal, Old_Total, Old_Joint, Old_Marginal));
   procedure Observe_Quantization
     (P : Long_Float; Before, After : Long_Long_Integer) with
     Ghost,
     Global => null,
     Pre => Quantization_Normal_Return (P, Before, After),
     Post => After = Before and then abs (Long_Float (After) / Long_Float (Scale) - P) <= 0.51E-15,
     Depends => (null => (P, Before, After));
   procedure Observe_Union (A, B, J, Old_A, Old_B, Old_J : Long_Long_Integer) with Ghost,
     Global => null,
     Pre => Union_Normal_Return (A, B, J, Old_A, Old_B, Old_J),
     Post => A = Old_A and then B = Old_B and then J = Old_J,
     Depends => (null => (A, B, J, Old_A, Old_B, Old_J));
   procedure Observe_Conditional (J, M, Old_J, Old_M : Long_Long_Integer) with Ghost,
     Global => null,
     Pre => Conditional_Normal_Return (J, M, Old_J, Old_M),
     Post => J = Old_J and then M = Old_M,
     Depends => (null => (J, M, Old_J, Old_M));
   procedure Observe_Joint (J, A, B, Old_J : Long_Float) with
     Ghost,
     Global => null,
     Pre => Joint_Normal_Return (J, A, B, Old_J),
     Post => J = Old_J and then J in 0.0 .. A and then J <= B,
     Depends => (null => (J, A, B, Old_J));
   procedure Observe_Inverse_Bracket (P, Lower_Tail, Upper_Tail : Long_Float) with Ghost,
     Global => null,
     Pre => P > Lower_Tail and P < Upper_Tail,
     Post => P > Lower_Tail and P < Upper_Tail,
     Depends => (null => (P, Lower_Tail, Upper_Tail));
end Towers_Boundary_Models;
