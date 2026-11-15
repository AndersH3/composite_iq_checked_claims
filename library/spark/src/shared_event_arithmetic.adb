--  Canonical exact integer event-probability implementation.
package body Shared_Event_Arithmetic with SPARK_Mode is
   function Union_Units (A, B, J : Units) return Units is
   begin
      --  Precondition permits the exact inclusive upper and lower bounds.
      return Units (A + B - J);
   end Union_Units;

   function Complement_Units (P : Units) return Units is
   begin
      --  The domain and codomain use the same exact unit scale.
      return Units (Scale_Units - P);
   end Complement_Units;
end Shared_Event_Arithmetic;
