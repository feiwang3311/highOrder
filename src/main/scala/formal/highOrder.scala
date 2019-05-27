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

  abstract class Num {
    def + (that: Num): Num
    def * (that: Num): Num
    val l: Int // layer
  }

  case class NumV(val x: Double) extends Num {
    def + (that: Num) = NumV(x + that.asInstanceOf[NumV].x)
    def * (that: Num) = NumV(x * that.asInstanceOf[NumV].x)
    override def toString = x.toString
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

  def liftF(x: Double, l: Int): Num =
    if (l == 0) NumV(x)
    else NumF(liftF(x, l-1), liftF(0, l-1))

  def grad(f: Num => Num) = (x: Num) => {
    val z = new NumF(x, liftF(1.0, x.l))
    f(z).asInstanceOf[NumF].d
  }

  // def liftR(x: Double, l: Int): Num =
  //   if (l == 0) NumV(x)
  //   else NumR(liftR(x, l-1), liftR(0, l-1))   

  // case class NumR(val x: Num, var d: Num) extends Num {
  //   def + (that: Num): Num@cps[Unit] = shift { k: (Num => Unit) =>
  //     val z = that.asInstanceOf[NumR]
  //     val y = new NumR(x + z.x, liftR(0.0, x.l))
  //     k(y)
  //     d = d + y.d
  //     z.d = z.d + y.d
  //   }
  //   def * (that: Num): Num@cps[Unit] = shift { k: (Num => Unit) =>
  //     val z = that.asInstanceOf[NumR]
  //     val y = new NumR(x * z.x, liftR(0.0, x.l))
  //     k(y)
  //     d = d + y.d * z.x
  //     z.d = z.d + y.d * x
  //   }
  //   val l = {
  //     assert(x.l == d.l)
  //     x.l + 1
  //   }
  // }

  // def grad(f: Num => Num@cps[Unit]) = (x: Num) => {
  //   val z = new NumR(x, liftR(0.0, x.l))
  //   continuations.reset{ f(z).asInstanceOf[NumR].d = liftR(1.0, x.l) }
  //   z.d
  // }

  def assertEqual(a: Num, b: Num) {
    if (a != b) {
      println(s"$a != $b")
      assert(false)
    }
  }

  def main(args: Array[String]) {
    System.out.println("Hello")
    val f = (x: Num) => x * x * x
    assertEqual(grad(f)(NumV(4.0)), NumV(48))
    println(grad(f)(NumV(4.0)))
    assertEqual(grad(grad(f))(NumV(4.0)), NumV(24))
    println(grad(grad(f))(NumV(4.0)))
    assertEqual(grad(grad(grad(f)))(NumV(4.0)), NumV(6))
    println(grad(grad(grad(f)))(NumV(4.0)))
    
  }
}
