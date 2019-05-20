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

object secOrder {

  type Cont = (Num => Unit) => Unit
  type diff = cpsParam[Cont, Cont]

  class Num(var x: Double, var d: Double) {
    def + (that: Num) = {(k: Num => Unit) =>
      val y = new Num(x + that.x, 0.0); k(y)
      this.d += y.d; that.d += y.d
    }
    def * (that: Num) = {(k: Num => Unit) =>
      val y = new Num(x * that.x, 0.0); k(y)
      this.d += y.d * that.x; that.d += y.d * x
    }
    def += (that: Num) = {(k: Num => Unit) =>
      this.x += that.x
      k(this)
      that.d += this.d
    }
    override def toString() = (x, d).toString
  }

  def gradd(f: Num => (Num => Unit) => Unit)(x: Double) = {
    val z = new Num(x, 0.0)
    var res = 0.0
    f(z){r => res = r.x; r.d = 1.0}
    (res, z.d)
  }

  class NumR(val x: Num, var d: Num) {
    def + (that: NumR) = shift { (k: NumR => Cont) =>
      (p: Num => Unit) => (x + that.x) { t: Num =>
        val y = new NumR(t, new Num(0.0, 0.0))
        k(y){u: Num =>
          (this.d += y.d){u: Num =>
            (that.d += y.d){u: Num =>
              p(u)
            }
          }
        }
      }
    }
    def * (that: NumR) = shift { (k: NumR => Cont) =>
      (p: Num => Unit) => (x * that.x) { t: Num =>
        val y = new NumR(t, new Num(0.0, 0.0))
        k(y){u: Num =>
          (y.d * that.x){u: Num =>
            (this.d += u){u: Num =>
              (y.d * this.x){u: Num =>
                (that.d += u)(p)
              }
            }
          }
        }
      }
    }
    override def toString() = (x.x, x.d, d.x, d.d).toString
  }

  def grad(f: NumR => NumR@diff)(x: Num) = {
    val z = new NumR(x, new Num(0.0, 0.0))
    continuations.reset{
      f(z).d.x = 1.0
      (p: Num => Unit) => p(new Num(0.0, 0.0))
    }
  }

  val input = new Num(5, 5)
  def f1(x: NumR) = x
  def f2(x: NumR) = x + x
  def f3(x: NumR) = x * x
  def f4(x: NumR) = x + x + x
  def f5(x: NumR) = x * x * x
  def f6(x: NumR) = x * x * x * x
  def f7(x: NumR) = x + x + x + x

  def main(args: Array[String]) {
    System.out.println("Hello")
    System.out.println(gradd(grad(f2))(5))
    System.out.println(gradd(grad(f3))(5))
    System.out.println(gradd(grad(f4))(5))
    System.out.println(gradd(grad(f5))(5))
    System.out.println(gradd(grad(f6))(5))
    System.out.println(gradd(grad(f7))(5))
  }
}
