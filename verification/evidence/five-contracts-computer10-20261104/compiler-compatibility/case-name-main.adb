with Ada.Text_IO; use Ada.Text_IO;
with Ada.Exceptions; use Ada.Exceptions;
with Towers_IO_Models; use Towers_IO_Models;
procedure Main is begin
 for K in 1..4 loop
  begin Put_Line (Case_Name(K)); exception when E:others=> Put_Line(Exception_Information(E)); end;
 end loop;
end Main;
