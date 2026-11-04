--  Deliberately incorrect fixture: success would invalidate the proof gate.
package Negative_Union with SPARK_Mode is
   subtype Count is Integer range 0 .. 1_000;
   function Union_Size (A, B, Joint : Count) return Integer with
     Global => null,
     Pre => Joint <= A and then Joint <= B,
     Post => Union_Size'Result = A + B - Joint,
     Depends => (Union_Size'Result => (A, B, Joint));
end Negative_Union;
