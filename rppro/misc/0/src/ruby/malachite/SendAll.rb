module SendAll

  def send_all(method_name, *args)
    methods.grep /#{method_name}/ do |m|
      self.send(m, *args)
    end
  end

  #def send_list(method_name, *names)
  #  names.each do |name|
  #    self.send method_name
  #  end
  #end
end

if $TEST

require 'test/unit'

class TestSendAll < Test::Unit::TestCase

  class Validator
    include SendAll
    alias_method :validate, :send_all

    def validate_a(arg)
      puts "a_#{arg}"
    end

    def validate_b(arg)
      puts "b_#{arg}"
    end

  end

  def test_1
    validator = Validator.new
    validator.validate('^validate_', 3)

    #validator.send_list 'validate_#{name}', :a, :b
  end
end

end # TEST

