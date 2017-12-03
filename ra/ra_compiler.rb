#!/usr/bin/env ruby

=begin
author: Igor Lesik 2013

Related projects:
 http://www.hokstad.com/compiler/
=end

require_relative 'function'
require_relative 'scope'
require_relative 'LocalVarScope'

class Compiler


  def initialize(out_dir)
    @out_dir = out_dir
    @string_literals = {}
    @literals_count = 0
    @exp_res_count = 0
    @lambda_count = 0
    @global_functions = {}
  end
  
  def compile(exp) 
    compile_main(exp) 
  end 

  def compile_main(exp)
    puts '#include "literals.h"'
    puts '#include "glbfundecl.h"'

    start = Function.new([],[])
    compile_exp(Scope.new(self, start), exp)

    output_functions("#{@out_dir}/glbfundecl.h")
    output_literals("#{@out_dir}/literals.h")

  end

  def compile_exp(scope, exp)
    return if !exp || exp.size == 0

    exp_head = exp[0]
    exp_tail = exp[1..-1]

    if exp_head == :do
      exp_tail.each { |e| compile_exp(scope, e) }
      return
    end

    if exp_head == :defun
      compile_define_function(scope, *exp_tail)
      return
    end

    if exp_head == :if
      compile_if_else(scope, *exp_tail)
      return
    end

    if exp_head == :let
      compile_let(scope,*exp_tail)
      return
    end

    if exp_head == :lambda
      compile_lambda(scope, *exp_tail)
      return
    end

    if exp_head == :call
      compile_call(scope, exp_tail[0], exp_tail[1])
      return
    end

    compile_call(scope, exp_head, exp_tail)
  end

  def compile_call(scope, func, args)

    # FIXME, lambda
    atype, aparam = compile_eval_arg(scope, func)
    #puts "// eval_arg: #{atype} #{aparam}"
    func_name=atype

    call_has_retval = func_name != :return

    call = func_name.to_s

    generated = ''
    if call_has_retval
      @exp_res_count += 1
      generated << "int exp_res_#{@exp_res_count} = #{call}("
    else
      generated << "#{call}("
    end

    evaluated_args = args.collect do |a|
      compile_eval_arg(scope, a)
    end

    generated << evaluated_args.join(',')
    generated << ");"
    puts generated

  end

  def compile_eval_arg(scope, arg)
      atype, aparam = get_arg(scope, arg)
      if atype == :str_literal
        val = "string_literal_#{aparam}"
      elsif atype == :subexpr
        val = "#{aparam}"
      elsif atype == :int
        val = "#{aparam}"
      elsif atype == :atom
        val = aparam #.to_s
      elsif atype == :arg
        val = "arg#{aparam}"
      elsif atype == :lvar
        val = "int #{aparam}"
      else
        val = 'oops'
      end
      val
  end

  def get_arg(scope, arg)

    # Handle subexpressions
    if arg.is_a?(Array)
      compile_exp(scope, arg)
      return [:subexpr, "exp_res_#{@exp_res_count}"]
    end

    # Handle integers
    return [:int, arg] if (arg.is_a?(Fixnum))

    return scope.get_arg(arg) if (arg.is_a?(Symbol)) 

    # Handle strings
    literal_id = @string_literals[arg]
    unless literal_id
      literal_id = @literals_count
      @literals_count += 1
      @string_literals[arg] = literal_id
    end
    return [:str_literal, literal_id]
  end

  def output_literals(file_name)
    File.open(file_name, "w") do |file|
      @string_literals.each do |literal,literal_id|
        file.puts "const char const string_literal_#{literal_id}[]="
        file.puts "  \"#{literal}\";"
      end
    end
  end

  def output_functions(glbfundecl_file)
    @global_functions.each do |name,func|
      puts "int"
      puts "#{name}("
puts func.args.join(",").to_s
      puts ")"
      puts "{"
      compile_exp(Scope.new(self, func), func.body)
      puts "}"
      puts
    end
	
    File.open(glbfundecl_file, "w") do |file|
      @global_functions.each do |name,data|
        file.puts "int"
        file.puts "#{name}();"
        file.puts
      end	
    end
  end
  
  def compile_define_function(scope, name, args, body)
    @global_functions[name] = Function.new(args, body)
    #return [:subexpr]
  end

  def compile_if_else cond, if_arm, else_arm 
    compile_exp(cond) 
    puts "if (exp_rcompilees_#{@exp_res_count}){" 
    compile_exp(if_arm) 
    puts "}" 
    puts "else {" 
    compile_exp(else_arm) 
    puts "}" 
  end

  def compile_lambda args, body
    name = "lambda__#{@lambda_count}"
    @lambda_count += 1
    @exp_res_count += 1
    puts "// #{name} #{args} #{body}"
    puts "int exp_res_#{@exp_res_count}(){puts(\"gcc extention\"); return 1;}"
    #DO NOT CALL define_function(name, args, body) because it is called from define_function
    return [:subexpr]
  end

  #def compile_do(scope,*exp)
  #  puts "// LET #{exp}"
  #  exp.each do |e|
  #    source=compile_eval_arg(scope,e);
  #    # @e.save_result(source);
  #    puts source
  #  end
  #  return [:subexpr]
  #end

  def compile_let(scope,varlist,*args)
    vars = {}
    varlist.each_with_index do |v,i|
      vars[v]=i
      puts "int #{v};"
    end
    ls = LocalVarScope.new(vars,scope)
    #@e.with_local(vars.size) { compile_do(ls,*args) }
    #compile_do(ls,*args)
  end

end #of class Compiler

