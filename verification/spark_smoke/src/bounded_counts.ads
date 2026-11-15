--  AI-assisted SPARK fixture: bounded nonnegative counter accumulation.
--
--  Purpose:
--    This standalone package tests whether GNATprove 16.1.0 can discharge
--    substantive functional and overflow contracts on computer10. It is
--    deliberately independent of project source and external libraries.
--    A successful run verifies only this proof obligation set, not the
--    statistical claims in the three reports.
--
--  Contract design:
--    The two preconditions separately establish a valid capacity and room
--    for the increment. The postconditions characterize exact accounting,
--    monotonicity, upper bounds, zero boundaries, and saturation. The
--    independent Global/Depends aspects establish the intended data flow.
--    These are behavioral properties, not arbitrary padding or assertions
--    that the statement is itself true.
package Bounded_Counts with SPARK_Mode => On is

   --  Add an increment to a bounded nonnegative count, without saturation
   --  or silent overflow. The caller supplies enough remaining capacity.
   --
   --  Preconditions:
   --    1. Previous is not larger than Capacity, so subtraction is safe.
   --    2. Increment fits into the remaining headroom.
   --
   --  Postconditions:
   --    1. Exact conservation of all increments.
   --    2. The declared capacity is never exceeded.
   --    3-4. Both nonnegative contributions bound the result.
   --    5-6. Each contribution is recoverable by exact subtraction.
   --    7. Zero total is equivalent to both contributions being zero.
   --    8-9. Equality with either input characterizes the other as zero.
   --   10. Exactly filling capacity characterizes remaining headroom.
   --
   --  Flow contracts additionally prohibit global state and declare
   --  dependency on precisely the two arithmetical inputs.
   procedure Accumulate
     (Previous  : in Natural;
      Increment : in Natural;
      Capacity  : in Natural;
      Total     : out Natural)
   with
     Global => null,
     Depends => (Total => (Previous, Increment)),
     Pre =>
       (Previous <= Capacity)
       and then (Increment <= Capacity - Previous),
     Post =>
       (Total = Previous + Increment)
       and then (Total <= Capacity)
       and then (Total >= Previous)
       and then (Total >= Increment)
       and then (Total - Previous = Increment)
       and then (Total - Increment = Previous)
       and then ((Total = 0) =
                 ((Previous = 0) and then (Increment = 0)))
       and then ((Total = Previous) = (Increment = 0))
       and then ((Total = Increment) = (Previous = 0))
       and then ((Total = Capacity) =
                 (Increment = Capacity - Previous));

end Bounded_Counts;
