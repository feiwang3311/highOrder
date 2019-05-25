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

object forwardShift {

  class Num(val x: Double, val d: Double) {
    def + (that: Num) = new Num(x + that.x, d + that.d)
    def * (that: Num) = new Num(x * that.x, d * that.x + x * that.d)
  }
  def grad(f: Num => Num)(x: Double) = {
    val z = new Num(x, 1.0)
    f(z).d
  }

  class NumR(val x: Num, var d: Num) {
    def + (that: NumR) = shift { k: (NumR => Unit) =>
      val y = new NumR(x + that.x, new Num(0.0, 0.0))
      k(y)
      d = d + y.d
      that.d = that.d + y.d
    }
    def * (that: NumR) = shift { k: (NumR => Unit) =>
      val y = new NumR(x * that.x, new Num(0.0, 0.0))
      k(y)
      d = d + y.d * that.x
      that.d = that.d + y.d * x
    }
  }

  def grad(f: NumR => NumR@cps[Unit])(x: Num) = {
    val z = new NumR(x, new Num(0.0, 0.0))
    continuations.reset{ f(z).d = new Num(1.0, 0.0) }
    z.d
  }

  // val input = new Num(5, 5)
  def f1(x: NumR) = x
  def f2(x: NumR) = x + x
  def f3(x: NumR) = x * x
  def f4(x: NumR) = x + x + x
  def f5(x: NumR) = x * x * x
  def f6(x: NumR) = x + x + x + x
  def f7(x: NumR) = x * x * x * x

  def main(args: Array[String]) {
    System.out.println("Hello")
    val a1: Num => Num = grad(f1)
    System.out.println(grad(a1)(5))
    val a2: Num => Num = grad(f2)
    System.out.println(grad(a2)(5))
    val a3: Num => Num = grad(f3)
    System.out.println(grad(a3)(5))
    val a4: Num => Num = grad(f4)
    System.out.println(grad(a4)(5))
    val a5: Num => Num = grad(f5)
    System.out.println(grad(a5)(5))
    val a6: Num => Num = grad(f6)
    System.out.println(grad(a6)(5))
    val a7: Num => Num = grad(f7)
    System.out.println(grad(a7)(5))
  }

}
