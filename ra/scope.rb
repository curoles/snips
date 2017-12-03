

class Scope
  def initialize compiler,func
    @c = compiler
    @func = func
  end

  def get_arg a
    a = a.to_sym
    @func.args.each_with_index {|arg,i| return [:arg,i] if arg == a }
    return [:atom,a]
  end
end

