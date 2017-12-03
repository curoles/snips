module SendToIV

  def send_to(iv_name, method, *args)
    iv = instance_variable_get "@#{iv_name}"
    iv.send(method, *args)
  end
end

if $TEST

require 'test/unit'

class TestSendToIV < Test::Unit::TestCase

  class Person
    attr_accessor :name, :age
    def initialize(name, age)
      @name = name
      @age = age
    end

    def grow(nr_years)
      @age += nr_years
    end
  end

  class Controller
    include SendToIV
    def initialize
      @igor = Person.new 'Igor', 41
      @anton = Person.new 'Anton', 9
    end
  end

  def test_View
    controller = Controller.new
    assert_equal(controller.send_to(:igor, :name), 'Igor')
    assert_equal(controller.send_to(:anton, :age), 9)
    controller.send_to(:anton, :grow, 3)
    assert_equal(controller.send_to(:anton, :age), 12)
  end
end

end # TEST

