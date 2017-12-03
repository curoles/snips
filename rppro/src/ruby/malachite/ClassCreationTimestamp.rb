module ClassCreationTimestamp

  attr_accessor :timestamp

  def self.included(base)
    #puts "module #{self} included in #{base}"
    #@old_class_new = base.method(:new)
    #p @old_class_new
  end

  def initialize_timestamp
    @timestamp = Time.now
  end
  
end

if $TEST

require 'test/unit'

class TestClassCreationTimestamp < Test::Unit::TestCase

  class TimeStamped
    include ClassCreationTimestamp
    def initialize
      initialize_timestamp
    end
  end

  def test_1
    tso = TimeStamped.new
    p tso
    puts tso.timestamp
  end
end

end # TEST

