--  Shared, exact equicorrelation numerator arithmetic (SPARK).
--  This report-neutral package owns the integer formula common to
--  Hoeflin/Ferguson equal-weight variance and Sequential covariance
--  eigenvalues. All arithmetic fits signed 64-bit under the precondition.
--  No floating-point approximation or Gaussian assumption is made here.
package Shared_Equicorrelation with SPARK_Mode is
   Scale_1000 : constant Long_Long_Integer := 1_000;

   --  Exact scaled compound-symmetry eigenvalue D(n,c) = 1000+(n-1)c.
   --  The twelve distinct cases check admissible signs, singleton,
   --  independent and perfect-correlation boundaries on both sides.
   function Numerator (N : Positive; C : Integer)
      return Long_Long_Integer with
      Global => null,
      Pre => N <= 1_000_000 and then C in -1_000 .. 1_000,
      Post =>
        Numerator'Result =
          Scale_1000 + Long_Long_Integer (C) * Long_Long_Integer (N - 1)
        and then Numerator'Result <=
          Scale_1000 * Long_Long_Integer (N)
        and then Numerator'Result >=
          Scale_1000 * (2 - Long_Long_Integer (N))
        and then (if N = 1 then Numerator'Result = Scale_1000)
        and then (if C = 0 then Numerator'Result = Scale_1000)
        and then (if C = 1_000 then
          Numerator'Result = Scale_1000 * Long_Long_Integer (N))
        and then (if C = -1_000 then
          Numerator'Result = Scale_1000 * (2 - Long_Long_Integer (N)))
        and then (if C >= 0 then
          Numerator'Result >= Scale_1000)
        and then (if C <= 0 then
          Numerator'Result <= Scale_1000)
        and then (if N >= 2 and C > 0 then
          Numerator'Result > Scale_1000)
        and then (if N >= 2 and C < 0 then
          Numerator'Result < Scale_1000)
        and then (if N >= 2 and C >= 0 then
          Numerator'Result >= Scale_1000 + Long_Long_Integer (C))
        and then (if N >= 2 and C <= 0 then
          Numerator'Result <= Scale_1000 + Long_Long_Integer (C)),
      Depends => (Numerator'Result => (N, C));
end Shared_Equicorrelation;
