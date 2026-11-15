--  AI-assisted SPARK proof fixture body for Bounded_Counts.
--
--  The implementation deliberately uses the ordinary checked addition
--  operation. GNATprove must show that the explicit capacity precondition
--  precludes overflow and that all ten accounting properties in the
--  specification follow from this exact assignment. No axiom, Assume,
--  unchecked conversion, suppression, or trusted non-SPARK body is used.
package body Bounded_Counts with SPARK_Mode => On is

   --  Functional implementation of the public contract. The specification
   --  is in bounded_counts.ads and contains the domain, data-flow,
   --  conservation, monotonicity, and boundary guarantees.
   procedure Accumulate
     (Previous  : in Natural;
      Increment : in Natural;
      Capacity  : in Natural;
      Total     : out Natural)
   is
   begin
      Total := Previous + Increment;
      --  The exact capacity check is an additional native assertion VC.
      --  It cannot be omitted or treated as an external assumption.
      pragma Assert (Total <= Capacity);
   end Accumulate;

end Bounded_Counts;
