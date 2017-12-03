class Object
  attr_accessor :timestamp
end

class Class

  alias_method :old_new, :new

  def new(*args, &b)
    result = old_new(*args, &b)
    result.timestamp = Time.now
    result
  end
end

if $TEST

require 'test/unit'

class TestAddTimestampToEveryObjectCreated < Test::Unit::TestCase

  class ClassA
  end

  def test_1
    a = ClassA.new
    #p a
    puts "object #{a} of type #{a.class} created #{a.timestamp}"
    assert(a.respond_to? :timestamp)
  end
end

end # TEST

