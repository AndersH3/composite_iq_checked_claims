with Ada.Text_IO; use Ada.Text_IO;
with Ada.Exceptions; use Ada.Exceptions;
with Admission_Core; use Admission_Core;
procedure Main is
 Result : Event;
begin
 for A in Boolean loop
  for B in Boolean loop
   Put_Line (Boolean'Image(A) & " " & Boolean'Image(B));
   begin
    Result := Classify (A,B); Put_Line (Event'Image(Result));
   exception when E:others => Put_Line(Exception_Information(E)); end;
  end loop;
 end loop;
end Main;
