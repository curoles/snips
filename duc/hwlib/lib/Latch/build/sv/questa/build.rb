=begin rdoc
 Description::  Latch build script.
 Author::       Igor Lesik 2014
 Copyright::    Igor Lesik 2014
=end

require 'fileutils'

class ModuleBuilder
  def get_source_files(src_root, src, tb)
    [ File.join(tb,  'Dve.sv'),
      File.join(tb,  'Latch_checker.sv'),
      File.join(src, 'Latch.v'),
      File.join(src_root, 'hwlib', 'sv', 'SimClkGen.sv')
    ]
  end
end

require File.join($module_attr[:src_root], 'hwlib', 'questa', 'sv_build')

