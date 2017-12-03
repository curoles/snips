#author    Igor Lesik
#copyright Igor Lesik 2013

module Mig1

module Format
  OP     = 0
  OP_OP  = 1
  OP_IMM = 2
end

module OpCode
  MOVE  = 0b0000 # Rop1 <- Rop2, move between R[0..3] registers; 00_00_0000 move R0 to R0 is NOP
  SET   = 0b0001 # Rop1 <- IMM32, set R[0..15] to IMM32
  STORE = 0b0010 # M[*Rop1] <- Rop2
  LOAD  = 0b0011 # Rop1 <- M[*Rop2]
  JUMP  = 0b0100 # branch to *Rop1
  RES1  = 0b0101
  RES2  = 0b0110
  RES3  = 0b0111
  RES4  = 0b1000
  RES5  = 0b1001
  RES6  = 0b1010
  RES7  = 0b1011
  RES8  = 0b1110
  RES9  = 0b1111

  @@format = {
    SET   => Format::OP_IMM,
    MOVE  => Format::OP_OP,
    STORE => Format::OP_OP,
    LOAD  => Format::OP_OP,
    JUMP  => Format::OP
  }
end

$ASSERTIONS_ENABLED=1

def Mig1.assert(*msg)
  raise "Assertion failed! #{msg}" unless yield if $ASSERTIONS_ENABLED
end

def Mig1.encode__op_op(opcode, op1, op2)
  op1.register?()
  op2.register?()
  assert("op1.reg_id < 4") {op1.reg_id < 4}
  assert("op2.reg_id < 4") {op2.reg_id < 4}
  insn = (op1.reg_id << 6) | (op2.reg_id << 4) | opcode
end

def Mig1.encode__op(opcode, op)
  op.register?
  assert("op1.reg_id < 16") {op.reg_id < 16}
  insn = (op.reg_id << 4) | opcode
end

class Register

  def self.register?()
    true
  end

end

class AsmProgram

  @@words = []

  def self.compile(output_file_name)
    @@words.each do  |word|
      puts("%08b" % word)
    end
  end

  def self.set(dst, src)
    dst.register?()
    puts("SET    #{dst.name} <-  #{src}")
  end

  def self.move(dst, src)
    dst.register?()
    src.register?()
    insn = Mig1::encode__op_op(OpCode::MOVE, dst, src)
    @@words.push(insn)
    puts("MOVE   #{dst.name} <-  #{src}   %08b" % insn)
  end

  def self.nop
    self.move(R0, R0)
  end

  def self.store(dst, src)
    dst.register?
    src.register?
    insn = Mig1::encode__op_op(OpCode::STORE, dst, src)
    @@words.push(insn)
    puts("STORE *#{dst.name} <-  #{src}   %08b" % insn)
  end

  def self.ld(dst, src)
    dst.register?
    src.register?
    insn = Mig1::encode__op_op(OpCode::LOAD, dst, src)
    @@words.push(insn)
    puts("LOAD   #{dst.name} <- *#{src}   %08b" % insn)
  end

  def self.jump(src)
    src.register?
    insn = Mig1::encode__op(OpCode::JUMP, src)
    @@words.push(insn)
    puts("JUMP  *#{src}          %08b" % insn)
  end

end

end # Mig1



# Define class for each register
16.times do |reg_id|
  #puts "define R#{reg_id}"
  eval <<DYNAMIC
    class R#{reg_id} < Mig1::Register
      def self.reg_id()
        #{reg_id}
      end
    end
DYNAMIC
end

