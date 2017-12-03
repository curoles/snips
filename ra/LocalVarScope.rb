class LocalVarScope

 def initialize locals, next_scope
   @next = next_scope
   @locals = locals
 end

  def get_arg a
    a = a.to_sym 
    return [:lvar,@locals[a]] if @locals.include?(a)
    return @next.get_arg(a) if @next
    return [:addr,a] # Shouldn't get here normally
  end

end 
