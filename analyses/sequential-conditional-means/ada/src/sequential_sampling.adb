
package body Sequential_Sampling with SPARK_Mode is
   --  Delegate all sqrt acceptance logic to the one shared checked
   --  numerical implementation; the report retains its specialized API.
   function Checked_Sqrt (X : Variance) return Root is
   begin
      return Shared_Normal_Sampling.Checked_Sqrt (X);
   end Checked_Sqrt;

   procedure Draw
     (G        : in out Shared_Normal_Sampling.Generator;
      Location : Location_Value;
      Sigma    : Sigma_Value;
      Sample   : out Sample_Value)
   is
      Noise, Unused_Noise : Shared_Normal_Sampling.Normal_Value;
   begin
      if Sigma = 0.0 then
         Sample := Location;
      else
         --  The second output belongs to the library's Box--Muller pair.  It
         --  is deliberately discarded rather than introducing hidden cached
         --  state; the explicit Generator contains all persistent draw state.
         Shared_Normal_Sampling.Normal_Pair (G, Noise, Unused_Noise);
         Sample := Location + Sigma * Noise;
      end if;
   end Draw;
end Sequential_Sampling;
