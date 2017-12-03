module ClassWithAttributes

  def initialize_attributes(attributes)
    attributes.each do |attr, val|
      ClassWithAttributes.instance_eval "attr_accessor :#{attr}"
      instance_variable_set("@#{attr}", val)
    end
  end

  def self.lazy_loaded_attr(*attributes)
    attributes.each do |attr|
      define_method(attr) do
        eval "@#{attr} ||= load_attr_#{attr}"
      end
    end
  end
end

if $TEST

require 'test/unit'

class TestClassWithAttributes < Test::Unit::TestCase

  class Person
    include ClassWithAttributes

    ClassWithAttributes.lazy_loaded_attr :story

    def initialize(attributes)
      initialize_attributes(attributes)
    end

    def load_attr_story
      "was born in Russia..."
    end
  end

  def test_1
    igor = Person.new :name => 'Igor', :age => 41, :sex => :male
    p igor
    assert_equal(igor.name, 'Igor')
    igor.name = 'IgorTheGreat'
    assert_equal(igor.name, 'IgorTheGreat')
    puts igor.story
  end
end

end # TEST

