package body Negative_Union with SPARK_Mode is
   function Union_Size (A, B, Joint : Count) return Integer is
   begin
      --  Intentionally adds the overlap instead of subtracting it.
      return A + B + Joint;
   end Union_Size;
end Negative_Union;
