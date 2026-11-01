--  Executable Ghost specifications of the checked numerical boundary.
--  These predicates describe accepted normal returns. They do not assert
--  transcendental accuracy or prove an off-mode implementation refines them.
package Towers_Boundary_Models with SPARK_Mode, Ghost is
   Scale : constant Long_Long_Integer := 1_000_000_000_000_000;

   function Sqrt_Normal_Return (X, Y : Long_Float) return Boolean
   is (Y in 0.0 .. 1.0E3
       and then (if X >= 1.0E-30 then Y >= 1.0E-15)
       and then (if X >= 0.0625 then Y >= 0.25)
       and then (if X >= 1.0 then Y >= 1.0)
       and then (if X <= 1.0 then Y <= 1.0)
       and then (if X <= 4.0 then Y <= 2.0)
       and then (if X <= 64.0 then Y <= 8.0));

   function Survival_Normal_Return (Z, P : Long_Float) return Boolean
   is (P in 0.0 .. 1.0
       and then (if Z >= 10.0 then P < 1.0E-20)
       and then (if Z <= -10.0 then P > 1.0 - 1.0E-14));

   function Log_Normal_Return (X, Y : Long_Float) return Boolean
   is (X in 4.0E-10 .. 0.9999999999 and then Y in -23.0 .. 0.0);

   function Exp_Normal_Return (X, Y : Long_Float) return Boolean
   is (X <= 1.0E-9 and then Y in 0.0 .. 1.0001);

   --  Range abstraction of an observed Sin/Cos value. The installed Ada
   --  specifications supply this bound; the backend and accuracy are unproved.
   function Trigonometric_Value (Value : Long_Float) return Boolean
   is (Value in -1.0 .. 1.0);

   function Exponent_Normal_Return (Before, After : Long_Float) return Boolean
   is (After = Before and then After <= 1.0E-9);

   function Probability_Normal_Return (Before, After : Long_Float) return Boolean
   is (After = Before and then After in 0.0 .. 1.0);

   function Node_Normal_Return (Before, After : Long_Float) return Boolean
   is (After = Before and then After in 0.0 .. 0.96);

   function Grid_Cell_Normal_Return
     (Total, Joint, Marginal : Long_Float) return Boolean
   is (Total in 1.0E-100 .. 1.0E6 and then
       Joint in 0.0 .. Total and then Marginal in 0.0 .. Total);

   function Quantization_Normal_Return
     (P : Long_Float; Before, After : Long_Long_Integer) return Boolean
   is (P in 0.0 .. 1.0 and then Before in 0 .. Scale
       and then After = Before and then
       abs (Long_Float (After) / Long_Float (Scale) - P) <= 0.51E-15);

   function Union_Normal_Return
     (A, B, J, Old_A, Old_B, Old_J : Long_Long_Integer) return Boolean
   is (A in 0 .. Scale and then B in 0 .. Scale and then J in 0 .. Scale
       and then A = Old_A and then B = Old_B and then J = Old_J
       and then J <= A and then J <= B and then A + B <= Scale);

   function Conditional_Normal_Return
     (J, M, Old_J, Old_M : Long_Long_Integer) return Boolean
   is (J in 0 .. Scale and then M in 1 .. Scale
       and then J = Old_J and then M = Old_M and then J <= M);

   function Joint_Normal_Return (J, A, B, Old_J : Long_Float) return Boolean
   is (A in 0.0 .. 1.0 and then B in 0.0 .. 1.0
       and then J = Old_J and then J in 0.0 .. A and then J <= B);

   --  A proved projection theorem about the model; it does not establish
   --  that erfc, integration, or a guard can never reject at runtime.
   procedure Project_Conditional
     (J, M, Old_J, Old_M : Long_Long_Integer)
     with Global => null,
     Pre => Conditional_Normal_Return (J, M, Old_J, Old_M),
     Post => M > 0 and J >= 0 and J <= M and J = Old_J and M = Old_M;

   procedure Project_Grid_Cell (Total, Joint, Marginal : Long_Float)
     with Global => null,
     Pre => Grid_Cell_Normal_Return (Total, Joint, Marginal),
     Post => Total > 0.0 and Joint >= 0.0 and Joint <= Total
       and Marginal >= 0.0 and Marginal <= Total;

   --  Calls in off-mode bodies check model coupling when Ghost is enabled.
   --  Their ghost-only preconditions are erased under Ghost=>Ignore while
   --  every original ordinary Post and concrete guard remains enabled.
   procedure Observe_Sqrt (X, Y : Long_Float)
     with Global => null, Pre => Sqrt_Normal_Return (X, Y);
   procedure Observe_Survival (Z, P : Long_Float)
     with Global => null, Pre => Survival_Normal_Return (Z, P);
   procedure Observe_Log (X, Y : Long_Float)
     with Global => null, Pre => Log_Normal_Return (X, Y);
   procedure Observe_Exp (X, Y : Long_Float)
     with Global => null, Pre => Exp_Normal_Return (X, Y);
   procedure Observe_Trig (Value : Long_Float)
     with Global => null, Pre => Trigonometric_Value (Value);
   procedure Observe_Exponent (Before, After : Long_Float)
     with Global => null, Pre => Exponent_Normal_Return (Before, After);
   procedure Observe_Probability (Before, After : Long_Float)
     with Global => null, Pre => Probability_Normal_Return (Before, After);
   procedure Observe_Node (Before, After : Long_Float)
     with Global => null, Pre => Node_Normal_Return (Before, After);
   procedure Observe_Grid_Cell
     (Total, Joint, Marginal, Old_Total, Old_Joint, Old_Marginal : Long_Float)
     with Global => null,
     Pre => Grid_Cell_Normal_Return (Total, Joint, Marginal)
       and Total = Old_Total and Joint = Old_Joint and Marginal = Old_Marginal;
   procedure Observe_Quantization
     (P : Long_Float; Before, After : Long_Long_Integer)
     with Global => null, Pre => Quantization_Normal_Return (P, Before, After);
   procedure Observe_Union (A, B, J, Old_A, Old_B, Old_J : Long_Long_Integer)
     with Global => null, Pre => Union_Normal_Return (A, B, J, Old_A, Old_B, Old_J);
   procedure Observe_Conditional (J, M, Old_J, Old_M : Long_Long_Integer)
     with Global => null, Pre => Conditional_Normal_Return (J, M, Old_J, Old_M);
   procedure Observe_Joint (J, A, B, Old_J : Long_Float)
     with Global => null, Pre => Joint_Normal_Return (J, A, B, Old_J);
   procedure Observe_Inverse_Bracket (P, Lower_Tail, Upper_Tail : Long_Float)
     with Global => null,
     Pre => P > Lower_Tail and P < Upper_Tail,
     Post => P > Lower_Tail and P < Upper_Tail;
end Towers_Boundary_Models;
