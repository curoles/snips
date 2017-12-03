package io

import java.io.File
import java.io.PrintWriter

import scala.reflect.runtime.universe._
import scala.reflect.{ClassTag,classTag}

trait FileTrait {

    /** Loan Pattern, opens resource and loans it to a function,
     *  when the function completes, resource gets closed.
     *
     */
    def withA[Resource <: java.io.Writer](resource: Resource, op: Resource => Unit) = {
        try {
            op(resource)
        }
        finally {
            resource.close()
        }
    }

    /**
     *   val file = new java.io.File("1.txt")
     *
     *   io.FileTool.withPrintWriter(file) {
     *       writer => writer.println(new java.util.Date)
     *   }
     */
    def withPrintWriter(file: File)(op: PrintWriter => Unit) = {
        withA(new PrintWriter(file), op)
    }
}

object FileTool extends FileTrait

