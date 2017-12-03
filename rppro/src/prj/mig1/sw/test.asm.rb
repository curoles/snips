require_relative 'mig1.asm.rb'

class Program < Mig1::AsmProgram

  nop
  set   R0, 0x03
  move  R1, R0
  move  R1, R3
  store R3, R1
  ld    R1, R3    
  jump  R1
end

Program.compile('test.txt')
