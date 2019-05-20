package lantern

import scala.util.continuations._
import scala.util.continuations
import org.scala_lang.virtualized.virtualize
import org.scala_lang.virtualized.SourceContext

import scala.virtualization.lms._
import scala.virtualization.lms.common._
import scala.collection.mutable.ArrayBuffer
import scala.collection.mutable.{Map => MutableMap}
import scala.math._

import scala.collection.mutable.ArrayBuffer

object Relay {

  type diff = cps[Unit]
  def RST(a: =>Unit @diff) = continuations.reset { a; () }
  val tape = ArrayBuffer.empty[Int => Unit ]

  class NumR(val x: Double, var d: Double) {
    def + (that: NumR) = shift {(k: NumR => Unit) =>
      val y = new NumR(x + that.x, 0.0); k(y)
      tape += (i => this.d += y.d)
      tape += (i => that.d += y.d)
      ()
    }
    def * (that: NumR) = shift {(k: NumR => Unit) =>
      val y = new NumR(x * that.x, 0.0); k(y)
      tape += (i => this.d += y.d * that.x)
      tape += (i => that.d += y.d * x)
      ()
    }
    override def toString() = (x, d).toString
  }

  def grad(f: NumR => NumR@diff)(x: Double) = {
    val z = new NumR(x, 0.0)
    RST{f(z).d = 1.0}
    tape.foreach{t => t(0)}
    z
  }

  def f1(x: NumR) = x
  def f2(x: NumR) = x + x
  def f3(x: NumR) = x + x + x
  def f4(x: NumR) = x * x
  def f5(x: NumR) = x * x * x
  def f6(x: NumR) = x + x * x + x

  def main(args: Array[String]) {
    System.out.println("Hello")
    System.out.println(grad(f1)(5))
    System.out.println(grad(f2)(5))
    System.out.println(grad(f3)(5))
    System.out.println(grad(f4)(5))
    System.out.println(grad(f5)(5))
    System.out.println(grad(f6)(5))
  }
}
