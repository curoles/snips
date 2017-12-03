=begin rdoc
 Description::  Mux build script.
 Author::       Igor Lesik 2014
 Copyright::    Igor Lesik 2014
=end

require 'fileutils'

class ModuleBuilder
  def get_source_files(src_root, src, tb)
    [ File.join(tb,  'Dve.sv'),
      File.join(tb,  'Mux_checker.sv'),
      File.join(src, 'Mux.v'),
      File.join(src, 'Mux2.v'),
      File.join(src, 'Mux3.v'),
      File.join(src_root, 'hwlib', 'sv', 'SimClkGen.sv'),
      File.join(src_root, 'hwlib', 'sv', 'SimRstGen.sv')
    ]
  end
end

require File.join($module_attr[:src_root], 'hwlib', 'questa', 'sv_build')

