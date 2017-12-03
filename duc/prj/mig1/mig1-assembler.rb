module Mig1

RFSZ = 2**9

#module Assembly

module Format
  OPC       = 0
  OPC_I     = 1
  OPC_R     = 2
  OPC_R_I   = 3
  OPC_R_R_R = 4
end

module Field
  FLD_OPC = 27; FLD_OPC_END = 31; FLD_OPC_SZ = 1 + FLD_OPC_END - FLD_OPC
  FLD_IMM =  0; FLD_IMM_END = 17; FLD_IMM_SZ = 1 + FLD_IMM_END - FLD_IMM
  FLD_R1  = 18; FLD_R1_END  = 26; FLD_R1_SZ  = 1 + FLD_R1_END  - FLD_R1
  FLD_R2  =  9; FLD_R2_END  = 17; FLD_R2_SZ  = 1 + FLD_R2_END  - FLD_R2
  FLD_R3  =  0; FLD_R3_END  =  8; FLD_R3_SZ  = 1 + FLD_R3_END  - FLD_R3
end

module OpCode
  OR    = 0b00000 # ooooorrrrrrrrrRRRRRRRRRrrrrrrrrr
  SET   = 0b00001 # ooooorrrrrrrrriiiiiiiiiiiiiiiiii
  JUMP  = 0b00010 # ooooorrrrrrrrr..................
  BR    = 0b00011 # ooooorrrrrrrrr..................
  BRI   = 0b00100 # ooooo.........iiiiiiiiiiiiiiiiii
  ADD   = 0b00101 # ooooorrrrrrrrrRRRRRRRRRrrrrrrrrr
  SUB   = 0b00110 # ooooorrrrrrrrrRRRRRRRRRrrrrrrrrr
  AND   = 0b00111 # ooooorrrrrrrrrRRRRRRRRRrrrrrrrrr
  XOR   = 0b01000 # ooooorrrrrrrrrRRRRRRRRRrrrrrrrrr
  RES5  = 0b01001
  RES6  = 0b01010
  RES7  = 0b01011
  RES8  = 0b01110
  RES9  = 0b01111
  SHL   = 0b10000
  SHR   = 0b10001
end #OpCode

@@format = {
  OpCode::OR    => Format::OPC_R_R_R,
  OpCode::SET   => Format::OPC_R_I,
  OpCode::JUMP  => Format::OPC_R,
  OpCode::BR    => Format::OPC_R,
  OpCode::BRI   => Format::OPC_I,
  OpCode::ADD   => Format::OPC_R_R_R
}

def get_insn_format(opcode)
  @@format[opcode]
end

#end #module Assembly


module Codec

include Field

$ASSERTIONS_ENABLED=1

def assert(*msg)
  raise "Assertion failed! #{msg}" unless yield if $ASSERTIONS_ENABLED
end

def encode__opc(opcode)
  insn = (opcode << FLD_OPC)
end

def encode__opc_r(opcode, reg)
  reg.register?
  assert("reg id < #{RFSZ}") {reg.id < RFSZ}
  insn = (opcode << FLD_OPC) | (reg.id << FLD_R1)
end

def encode__opc_r_i(opcode, reg, imm)
  reg.register?
  assert("reg id < #{RFSZ}") {reg.id < RFSZ}
  assert("src is numeric imm") {imm.is_a? Numeric}
  assert("imm < 2^#{FLD_IMM_SZ}") {imm < 2**FLD_IMM_SZ}

  insn = (opcode << FLD_OPC) | (reg.id << FLD_R1) | (imm << FLD_IMM)
end

def encode__opc_r_r_r(opcode, r1, r2, r3)
  r1.register?; r2.register?; r3.register?
  assert("reg id < #{RFSZ}") {r1.id < RFSZ and r2.id < RFSZ and r3.id < RFSZ}
  insn = (opcode << FLD_OPC) | (r1.id << FLD_R1) | (r2.id << FLD_R2) | (r3.id << FLD_R3)
end

end #module Codec



module AsmProgram

include Codec


class Register

  def self.register?()
    true
  end

end

# Define class for each register
RFSZ.times do |reg_id|
  #puts "define R#{reg_id}"
  eval <<DYNAMIC
    class R#{reg_id} < Register
      def self.id()
        #{reg_id}
      end
    end
DYNAMIC
end

  def compile(input_file, output_file)
    translate(input_file)
    @words.each do  |word|
      puts("%032b" % word)
    end
  end

  def set(dst, src)
    dst.register?()
    assert("src is numeric imm") {src.is_a? Numeric}
    insn = encode__opc_r_i(OpCode::SET, dst, src)
    @words.push(insn)
    puts("SET R#{dst.id} <- #{src}/0x#{src.to_s(16)}")
  end

  def or(dst, src1, src2)
    dst.register?; src1.register?; src2.register?
    insn = encode__opc_r_r_r(OpCode::OR, dst, src1, src2)
    @words.push(insn)
    puts("OR R#{dst.id} <- R#{src1.id} | R#{src2.id}")
  end

  def nop
    self.or(R0, R0, R0)
    puts("NOP")
  end

end


class Program
  include AsmProgram

  def initialize
    @words = []
  end

  def translate(file='test1.S')
    eval File.read(file)
  end
end

end #module Mig1


Mig1::Program.new.compile('test1.S', 'test.txt')


