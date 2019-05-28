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

object highOrder {

  type diff = cps[Unit]

  abstract class Num {
    def + (that: Num): Num
    def * (that: Num): Num
    val l: Int // layer
    override def toString: String
  }

  case class NumV(val x: Double) extends Num {
    def + (that: Num) = NumV(x + that.asInstanceOf[NumV].x)
    def * (that: Num) = NumV(x * that.asInstanceOf[NumV].x)
    val l = 0
  }

  case class NumF(val x: Num, val d: Num) extends Num {
    def + (that: Num) = {
      val z = that.asInstanceOf[NumF]
      new NumF(x + z.x, d + z.d)
    }
    def * (that: Num) = {
      val z = that.asInstanceOf[NumF]
      new NumF(x * z.x, d * z.x + x * z.d)
    }
    override def toString = (x.toString, d.toString).toString
    val l = {
      assert(x.l == d.l)
      x.l + 1
    }
  }

  // var counter = -1
  // def getTag = {
  //   counter += 1
  //   counter
  // }

  def liftF(x: Double, l: Int): Num = {
    assert(l >= 0)
    if (l == 0) NumV(x)
    else NumF(liftF(x, l-1), liftF(0, l-1))
  }

  def grad(f: Num => Num) = (x: Num) => {
    val z = new NumF(x, liftF(1.0, x.l))
    f(z).asInstanceOf[NumF].d
  }

  case class NumR(val x: Num, var d: Num) {
    def + (z: NumR) = shift { k: (NumR => Unit) =>
      // val z = that.asInstanceOf[NumR]
      val y = new NumR(x + z.x, liftF(0.0, x.l))
      k(y)
      d = d + y.d
      z.d = z.d + y.d
    }
    def * (z: NumR) = shift { k: (NumR => Unit) =>
      // val z = that.asInstanceOf[NumR]
      val y = new NumR(x * z.x, liftF(0.0, x.l))
      k(y)
      d = d + y.d * z.x
      z.d = z.d + y.d * x
    }
    val l = {
      assert(x.l == d.l)
      x.l + 1
    }
  }

  case class Overloaded1()
  implicit val o1: Overloaded1 = Overloaded1()
  def grad(f: NumR => NumR@cps[Unit])(implicit o: Overloaded1) = (x: Num) => {
  // def grad1(f: NumR => NumR@cps[Unit]) = (x: Num) => {
    val z = new NumR(x, liftF(0.0, x.l))
    continuations.reset{ f(z).d = liftF(1.0, x.l) }
    z.d
  }

  case class NumR0(val x: Num, var d: Num) {
    def + (z: NumR0) = {k: (NumR0 => Unit) =>
      val y = new NumR0(x + z.x, liftF(0.0, x.l))
      k(y)
      d = d + y.d
      z.d = z.d + y.d
    }
    def * (z: NumR0) = {k: (NumR0 => Unit) =>
      val y = new NumR0(x * z.x, liftF(0.0, x.l))
      k(y)
      d = d + y.d * z.x
      z.d = z.d + y.d * x
    }
    val l = {
      assert(x.l == d.l)
      x.l + 1
    }
  }

  case class Overloaded2()
  implicit val o2: Overloaded2 = Overloaded2()
  def grad(f: NumR0 => (NumR0 => Unit) => Unit)(implicit o: Overloaded2) = (x: Num) => {
    val z = new NumR0(x, liftF(0.0, x.l))
    f(z)(r => r.d = liftF(1.0, x.l))
    z.d
  }

  type Cont = (NumR0 => Unit) => Unit
  class NumRR(val x: NumR0, var d: NumR0) {
    def + (that: NumRR) = shift { (k: NumRR => Cont) =>
      (p: NumR0 => Unit) => (x + that.x) { t: NumR0 =>
        val y = new NumRR(t, new NumR0(liftF(0.0, x.l - 1), liftF(0.0, x.l - 1)))
        k(y){u: NumR0 =>
          (this.d + y.d){u: NumR0 =>
            this.d = u;
            (that.d + y.d){u: NumR0 =>
              that.d = u
              p(that.d)
            }
          }
        }
      }
    }
    def * (that: NumRR) = shift { (k: NumRR => Cont) =>
      (p: NumR0 => Unit) => (x * that.x) { t: NumR0 =>
        val y = new NumRR(t, new NumR0(liftF(0.0, x.l - 1), liftF(0.0, x.l - 1)))
        k(y){u: NumR0 =>
          (y.d * that.x){u: NumR0 =>
            (this.d + u){u: NumR0 =>
              this.d = u
              (y.d * this.x){u: NumR0 =>
                (that.d + u){u: NumR0 =>
                  that.d = u
                  p(that.d)
                }
              }
            }
          }
        }
      }
    }
    override def toString() = (x.x, x.d, d.x, d.d).toString
  }

  case class Overloaded3()
  implicit val o3: Overloaded3 = Overloaded3()
  def grad(f: NumRR => NumRR@cps[Cont])(implicit o: Overloaded3) = (x: NumR0) => {
    val z = new NumRR(x, new NumR0(liftF(0.0, x.l - 1), liftF(0.0, x.l - 1)))
    reset{
      f(z).d = new NumR0(liftF(1.0, x.l - 1), liftF(0.0, x.l - 1))
      (p: NumR0 => Unit) => p(z.d)
    }
  }

  def assertEqual(a: Num, b: Num) {
    if (a != b) {
      println(s"$a != $b")
      assert(false)
    }
  }

  def main(args: Array[String]) {

    println("forward mode AD")
    val f = (x: Num) => x * x * x
    assertEqual(grad(f)(NumV(4.0)), NumV(48))
    println(grad(f)(NumV(4.0)))
    assertEqual(grad(grad(f))(NumV(4.0)), NumV(24))
    println(grad(grad(f))(NumV(4.0)))
    assertEqual(grad(grad(grad(f)))(NumV(4.0)), NumV(6))
    println(grad(grad(grad(f)))(NumV(4.0)))

    println("reverse mode AD via shift/reset")
    val g = (x: NumR) => x * x * x
    val g1 = grad(g)
    val g2 = grad(grad(g))
    val g3 = grad(grad(grad(g)))
    assertEqual(g1(NumV(4.0)), NumV(48))
    println(g1(NumV(4.0)))
    assertEqual(g2(NumV(4.0)), NumV(24))
    println(g2(NumV(4.0)))
    assertEqual(g3(NumV(4.0)), NumV(6))
    println(g3(NumV(4.0)))

    println("reverse mode AD via cps")
    val h = (x: NumR0) => (k: NumR0 => Unit) => (x * x)(r => (r * x)(k))
    val h1 = grad(h)
    val h2 = grad(grad(h))
    val h3 = grad(grad(grad(h)))
    assertEqual(h1(NumV(4.0)), NumV(48))
    println(h1(NumV(4.0)))
    assertEqual(h2(NumV(4.0)), NumV(24))
    println(h2(NumV(4.0)))
    assertEqual(h3(NumV(4.0)), NumV(6))
    println(h3(NumV(4.0)))

    println("reverse mode AD via cps inside reverse mode AD via shift/reset")
    def t(x: NumRR) = x * x * x
    val t1: NumR0 => (NumR0 => Unit) => Unit = grad(t)
    val t2 = grad(t1)
    val t3 = grad(grad(t1))
    assertEqual(t2(NumV(4.0)), NumV(24))
    println(t2(NumV(4.0)))
    assertEqual(t3(NumV(4.0)), NumV(6))
    println(t3(NumV(4.0)))

    println("perturbation confusion")
    val a = grad { x: Num =>
      val shouldBeOne = grad((y: Num) => x + y)(NumV(1)) // Evaluates to 2 instead of 1! Unexpected.
      x * NumF(shouldBeOne, NumV(0))
    }(NumV(1))
    println(a)
  }
}
