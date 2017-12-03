=begin rdoc
 Description::  Dff build script.
 Author::       Igor Lesik 2014
 Copyright::    Igor Lesik 2014
=end

require 'fileutils'

class ModuleBuilder
  def get_source_files(src_root, src, tb)
    [ File.join(tb,  'Dve.sv'),
      File.join(tb,  'Dff_checker.sv'),
      File.join(src, 'Dff.v')
    ]
  end
end

require File.join($module_attr[:src_root], 'hwlib', 'questa', 'sv_build')

