=begin rdoc
 Description::  Mux Verilator build script.
 Author::       Igor Lesik 2014
 Copyright::    Igor Lesik 2014
=end

require 'fileutils'

class ModuleBuilder
  def get_source_files(src_root, src, tb)
    [ File.join(tb,  'Dve.v'),
      File.join(src, 'Mux2.v'),
      File.join(src, 'Mux3.v'),
      File.join(src, 'Mux.v')
    ]
  end
end

require File.join($module_attr[:src_root], 'hwlib', 'verilator', 'v_build')

