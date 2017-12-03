=begin rdoc

Description::  HW module base class
Copyright::    Igor Lesik 2013
Author::       Igor Lesik
License::      Distributed under the Boost Software License, Version 1.0.
               (See  http://www.boost.org/LICENSE_1_0.txt)

=end

require_relative '../malachite/ClassLevelInheritableAttributes'

module Hw


class Module

  include ClassLevelInheritableAttributes

  inheritable_attributes :inputs, :outputs, :nr_inputs, :nr_outputs
  @inputs = { }
  @outputs = { }
  @nr_inputs = 0
  @nr_outputs = 0


  def self.input(name, width = 1)
    @nr_inputs += 1
    @inputs[name] = {:width => width}
  end

  def self.output(name, width = 1)
    @nr_outputs += 1
    @outputs[name] = {:width => width}
  end

  inheritable_attributes :nr_parameters
  @nr_parameters = 0

  def self.parameter(name, val)
    @nr_parameters += 1
    inheritable_attributes name
    instance_variable_set("@#{name}", val)
  end

  def self.make(parameters)
    new_module = Class.new(self) do
      parameters.each do |param_name, param_val|
        instance_variable_set("@#{param_name}", param_val) #TODO if variable exists
      end
    end
    new_module
  end

  class << self; alias_method '[]', 'make'; end

  def self.define(module_definition)
    eval %(
      Class.new(Hw::Module) do
        #{module_definition}
      end
    )
  end

end



if $TEST

require 'test/unit'


class TestHwModel < Test::Unit::TestCase

  def module_And2(width = 1)
    Hw::Module.define(%(
      parameter :width, #{width}

      input  :in1, width
      input  :in2, width
      output :out, width
    ))
  end

  class And2 < Hw::Module
    parameter :width, 3

    input  :in1, width
    input  :in2, width
    output :out, width

  end

  def test_1
    #puts And2.inheritable_attributes
    assert_equal(2, And2.nr_inputs)
    assert_equal(1, And2.nr_outputs)
    assert_equal(1, And2.nr_parameters)
    assert_equal(3, And2.width)
    assert_equal(And2.width, And2.inputs[:in1][:width])
    assert_equal(And2.width, And2.inputs[:in2][:width])
    assert_equal(And2.width, And2.outputs[:out][:width])

    mAnd2_w4 = And2[:width => 4]
    assert_equal(4, mAnd2_w4.width)
    and2 = And2.new
  end

  def test_2
    mAnd2_w4 = module_And2(4)
    assert_equal(2, mAnd2_w4.nr_inputs)
    assert_equal(1, mAnd2_w4.nr_outputs)
    assert_equal(1, mAnd2_w4.nr_parameters)
    assert_equal(4, mAnd2_w4.width)
    assert_equal(mAnd2_w4.width, mAnd2_w4.inputs[:in1][:width])
    assert_equal(mAnd2_w4.width, mAnd2_w4.inputs[:in2][:width])
    assert_equal(mAnd2_w4.width, mAnd2_w4.outputs[:out][:width])

    and2 = mAnd2_w4.new
  end

end

end # TEST


end # Hw
