--  Shared exact probability-unit arithmetic for the Towers event model.
--  Only additive, discrete inclusion-exclusion and complement laws occur;
--  Gaussian assumptions, quadrature and estimated parameters remain with
--  the specialized admissions application.
package Shared_Event_Arithmetic with SPARK_Mode is
   Scale_Units : constant Long_Long_Integer := 1_000_000_000_000_000;
   subtype Units is Long_Long_Integer range 0 .. Scale_Units;

   --  Union has a feasible joint overlap: 0<=J<=min(A,B), A+B<=1.
   function Union_Units (A, B, J : Units) return Units with
      Global => null,
      Pre => J <= A and then J <= B
        and then A + B <= Scale_Units,
      Post =>
        Union_Units'Result = A + B - J
        and then Union_Units'Result >= A
        and then Union_Units'Result >= B
        and then Union_Units'Result <= A + B
        and then Union_Units'Result <= Scale_Units
        and then (if J = 0 then Union_Units'Result = A + B)
        and then (if J = A then Union_Units'Result = B)
        and then (if J = B then Union_Units'Result = A)
        and then (if A = 0 then Union_Units'Result = B)
        and then (if B = 0 then Union_Units'Result = A)
        and then (if A = B and J = A then
          Union_Units'Result = A),
      Depends => (Union_Units'Result => (A, B, J));

   --  Complement is an exact involution over integer probability units.
   function Complement_Units (P : Units) return Units with
      Global => null,
      Post =>
        Complement_Units'Result = Scale_Units - P
        and then Complement_Units'Result + P = Scale_Units
        and then (if P = 0 then Complement_Units'Result = Scale_Units)
        and then (if P = Scale_Units then Complement_Units'Result = 0)
        and then (if P > 0 then Complement_Units'Result < Scale_Units)
        and then (if P < Scale_Units then Complement_Units'Result > 0)
        and then (if P <= Scale_Units / 2 then
          Complement_Units'Result >= Scale_Units / 2)
        and then (if P >= Scale_Units / 2 then
          Complement_Units'Result <= Scale_Units / 2)
        and then (if P = Scale_Units / 2 then
          Complement_Units'Result = Scale_Units / 2)
        and then (if P > Scale_Units / 2 then
          Complement_Units'Result < Scale_Units / 2),
      Depends => (Complement_Units'Result => P);
end Shared_Event_Arithmetic;
