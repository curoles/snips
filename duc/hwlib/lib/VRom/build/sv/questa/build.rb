=begin rdoc
 Description::  Verilog ROM build script.
 Author::       Igor Lesik 2014
 Copyright::    Igor Lesik 2014
=end

require 'fileutils'

class ModuleBuilder
  def get_source_files(src_root, src, tb)
    [ File.join(tb,  'Dve.sv'),
      File.join(src, 'VRom.v'),
      File.join(src_root, 'hwlib', 'sv', 'SimClkGen.sv'),
      File.join(src_root, 'hwlib', 'sv', 'SimRstGen.sv')
    ]
  end
end

require File.join($module_attr[:src_root], 'hwlib', 'questa', 'sv_build')

