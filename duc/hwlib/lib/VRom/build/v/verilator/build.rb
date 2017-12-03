=begin rdoc
 Description::  Verilog ROM Verilator build script.
 Author::       Igor Lesik 2014
 Copyright::    Igor Lesik 2014
=end

require 'fileutils'

class ModuleBuilder
  def get_source_files(src_root, src, tb)
    [ File.join(tb,  'Dve.v'),
      File.join(src, 'VRom.v')
    ]
  end
end

require File.join($module_attr[:src_root], 'hwlib', 'verilator', 'v_build')

