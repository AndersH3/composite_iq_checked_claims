--  Shared normal-sampling regression: deterministic seed, adapter parity,
--  bounded sqrt endpoints and Sequential's deterministic zero-SD case.
--  Runtime checks are not proofs of Gaussian distributions or libm accuracy.
with Interfaces;
with Normal_Support;
with Sequential_Sampling;
with Shared_Normal_Sampling;
procedure Shared_Normal_Smoke is
   package S renames Shared_Normal_Sampling;
   package H renames Normal_Support;
   package Q renames Sequential_Sampling;
   use type Interfaces.Unsigned_64;
   A, B : S.Generator;
   U, V : S.Open_Unit;
   X, Y, HX, HY : S.Normal_Value;
   Sample : Q.Sample_Value;
   Before : Interfaces.Unsigned_64;
begin
   S.Reset (A, 0);
   S.Uniform (A, U);
   if A.State /= 1_442_695_040_888_963_407 then
      raise Program_Error with "LCG recurrence changed";
   end if;
   if U <= 0.0 or else U >= 1.0 then
      raise Program_Error with "uniform midpoint outside open unit";
   end if;

   S.Reset (A, 42);
   H.Reset (B, 42);
   for I in 1 .. 32 loop
      S.Uniform (A, U);
      H.Uniform (B, V);
      if U /= V or else A.State /= B.State then
         raise Program_Error with "Hoeflin adapter diverged in Uniform";
      end if;
   end loop;

   S.Reset (A, 42);
   H.Reset (B, 42);
   for I in 1 .. 32 loop
      S.Normal_Pair (A, X, Y);
      H.Normal_Pair (B, HX, HY);
      if X /= HX or else Y /= HY or else A.State /= B.State then
         raise Program_Error with "Hoeflin adapter diverged in Normal_Pair";
      end if;
   end loop;

   if S.Checked_Sqrt (0.0) /= 0.0
     or else S.Checked_Sqrt (1.0) /= 1.0
     or else S.Checked_Sqrt (4.0) /= 2.0
     or else Q.Checked_Sqrt (4.0) /= 2.0
   then
      raise Program_Error with "bounded square-root endpoint regression";
   end if;

   S.Reset (A, 17);
   Before := A.State;
   Q.Draw (A, 12.0, 0.0, Sample);
   if Sample /= 12.0 or else Before /= A.State then
      raise Program_Error with "zero-SD Sequential draw changed state";
   end if;
end Shared_Normal_Smoke;
