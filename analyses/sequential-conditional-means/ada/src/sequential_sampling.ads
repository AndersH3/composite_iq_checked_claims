with Interfaces;
with Shared_Normal_Sampling;

--  Narrow numerical and simulation boundary for the sequential analysis.
--  The exact Gaussian laws of the scalar aggregates are proved in the paper;
--  no contract here asserts that a deterministic finite-state PRNG generates
--  an exact normal distribution.  Shared_Normal_Sampling supplies the existing bounded
--  Box--Muller implementation rather than duplicating it in this analysis.
package Sequential_Sampling with SPARK_Mode is
   use type Interfaces.Unsigned_64;

   subtype Real is Shared_Normal_Sampling.Real;
   subtype Variance is Real range 0.0 .. 4.0;
   subtype Root is Real range 0.0 .. 2.0;
   subtype Location_Value is Real range -10_000.0 .. 10_000.0;
   subtype Sigma_Value is Real range 0.0 .. 2.0;
   subtype Sample_Value is Real range -10_020.0 .. 10_020.0;

   --  The shared numerical boundary delegates to Ada's elementary-functions library and
   --  checks every advertised numerical property before returning.  Its body
   --  is deliberately outside SPARK: these checked normal-return promises are
   --  a trusted numerical boundary, not a proof of libm's accuracy or a bound
   --  for the decimal-to-binary conversion of the variance supplied by callers.
   function Checked_Sqrt (X : Variance) return Root with
     Global => null,
     Depends => (Checked_Sqrt'Result => X),
     Post => Checked_Sqrt'Result >= 0.0
       and then Checked_Sqrt'Result <= 2.0
       and then (if X = 0.0 then Checked_Sqrt'Result = 0.0)
       and then (if X > 0.0 then Checked_Sqrt'Result > 0.0)
       and then (if X = 1.0 then Checked_Sqrt'Result = 1.0)
       and then (if X = 4.0 then Checked_Sqrt'Result = 2.0)
       and then (if X <= 1.0 then Checked_Sqrt'Result <= 1.0)
       and then (if X >= 1.0 then Checked_Sqrt'Result >= 1.0)
       and then abs (Checked_Sqrt'Result * Checked_Sqrt'Result - X)
         <= 1.0E-12;

   --  Draw a single scalar aggregate instead of constructing a complete test
   --  vector.  The caller supplies the aggregate's analytic location and SD.
   --  The centrally owned normal implementation has output in [-9,9], so the supported
   --  scales imply a displacement of at most 18 (at most 9 for unit scale).
   --  Zero SD is deterministic and consumes no random state.  The state flow
   --  excludes Location, which cannot affect which PRNG values are consumed.
   procedure Draw
     (G        : in out Shared_Normal_Sampling.Generator;
      Location : Location_Value;
      Sigma    : Sigma_Value;
      Sample   : out Sample_Value)
   with
     Global => null,
     Depends => (G => (G, Sigma), Sample => (G, Location, Sigma)),
     Post => Sample >= Location - 18.0
       and then Sample <= Location + 18.0
       and then (if Sigma = 0.0 then Sample = Location)
       and then (if Sigma = 0.0 then G.State = G.State'Old)
       and then (if Sigma <= 1.0 then Sample >= Location - 9.0)
       and then (if Sigma <= 1.0 then Sample <= Location + 9.0);
end Sequential_Sampling;
