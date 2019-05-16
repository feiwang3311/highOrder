package lantern

import scala.util.continuations._
import org.scala_lang.virtualized.virtualize
import org.scala_lang.virtualized.SourceContext

import scala.virtualization.lms._
import scala.virtualization.lms.common._
import scala.collection.mutable.ArrayBuffer
import scala.collection.mutable.{Map => MutableMap}
import scala.math._

object lang {

  abstract class Exp
  case class Const(a: Any) extends Exp
  case class Sym(b: Int) extends Exp
  case class Add(a: Exp, b: Exp) extends Exp
  // case class Mul(a: Exp, b: Exp) extends Exp
  case class Lam(x: Sym, e: Exp) extends Exp
  case class App(a: Exp, b: Exp) extends Exp
  case class Let(x: Sym, a: Exp, b: Exp) extends Exp
  case class Pair(a: Exp, b: Exp) extends Exp
  case class Fst(a: Exp) extends Exp
  case class Snd(a: Exp) extends Exp
  case class Ref(a: Exp) extends Exp
  case class Deref(a: Exp) extends Exp
  case class Assign(a: Exp, b: Exp) extends Exp
  // injection case shift reset

  var counter = 0
  def next() = {
    val temp = counter
    counter += 1
    temp
  }

  def trans(e: Exp): Exp @cps[Exp] = e match {
    case Const(a: Float) =>
      Pair(Const(a), Ref(Const(0)))
    case Const(a) => Const(a)
    case Sym(b)   => Sym(b) // no syntactic sugar
    // case Add(a, b) =>
    //   val y1 = Sym(next())
    //   val y2 = Sym(next())
    //   val y3 = Sym(next())
    //   Let(y1, trans(a),
    //     Let(y2, trans(b),
    //       shift { (k: Exp => Exp) =>
    //         Let(y3, Pair(Add(Fst(y1), Fst(y2)), Ref(Const(0))),
    //           Let(Sym(-1), k(y3),
    //             Let(Sym(-1), Assign(Snd(y1), Add(Deref(Snd(y1)), Deref(Snd(y3)))),
    //               Assign(Snd(y2), Add(Deref(Snd(y2)), Deref(Snd(y3)))))))
    //       }
    //     )
    //   )
    case Add(a, b) =>
      val y1 = Sym(next())
      val y2 = Sym(next())
      val y3 = Sym(next())
        shift { (k: Exp => Exp) =>
    reset{Let(y1, trans(a),
            Let(y2, trans(b),
              Let(y3, Pair(Add(Fst(y1), Fst(y2)), Ref(Const(0))),
                Let(Sym(-1), k(y3),
                  Let(Sym(-1), Assign(Snd(y1), Add(Deref(Snd(y1)), Deref(Snd(y3)))),
                    Assign(Snd(y2), Add(Deref(Snd(y2)), Deref(Snd(y3)))))))))}
        }
    case Lam(x, e) =>
      val k = Sym(next())
      Lam(x, Lam(k, reset{ App(k, trans(e)) }))

    case App(a, b) => shift { (k: Exp => Exp) =>
      reset{
        val y = Sym(next())
        App(App(trans(a), trans(b)), Lam(y, k(y)))
      }
    }

    case Let(y, a, b) => shift { (k: Exp => Exp) =>
      reset{
        Let(y, trans(a), reset{ k(trans(b)) })
      }
    }
    // case Let(y, a, b) =>
    //   Let(y, trans(a), shift { (k: Exp => Exp) =>
    //     reset{ k(trans(b)) }
    // })
  }

  def show(e: Exp, indent: Int): Unit = e match {
    case Const(a) => println(s"${"  " * indent}$a")
    case Sym(a) => println(s"${"  " * indent}$e")
    case Add(a, b) => println(s"${"  " * indent}$a + $b")
    case Let(x, a, b) =>
      print(s"${"  " * indent}$x = "); show(a);
      show(b, indent + 1)
    case App(a, b) => print("@ "); show(a); print("applyTo ====> "); show(b)
    case Lam(x, e) => print(s"$x => "); show(e)
    case a => println(s"${"  " * indent}$a")
  }

  def show(e: Exp): Unit = show(e, 0)

  val term: Exp = Const("Hello")
  val term0: Exp = Const(1.0f)
  val term1: Exp = Add(Const(1.0f), Const(2.0f))
  val term2: Exp = Add(Add(Const(1.0f), Const(2.0f)), Const(3.0f))
  val term3: Exp = Add(Const(3.0f), Add(Const(1.0f), Const(2.0f)))
  val x = Sym(next())
  val term4: Exp = App(Lam(x, Add(x, x)), Const(1.0f))
  val term5: Exp = Let(x, Const(1.0f), Add(x, x))

  def main(args: Array[String]) {
    println("term")
    val t = reset{ trans(term) }
    show(t)
    println("term0")
    show(reset{
      Assign(Snd(trans(term0)), Const(1.0f))
    })
    println("term1")
    val t1 = reset{
      Assign(Snd(trans(term1)), Const(1.0f))
    }
    show(t1)
    println("term2")
    val t2 = reset {
      Assign(Snd(trans(term2)), Const(1.0f))
    }
    show(t2)
    println("term3")
    val t3 = reset {
      Assign(Snd(trans(term3)), Const(1.0f))
    }
    show(t3)
    println("term4")
    val t4 = reset {
      Assign(Snd(trans(term4)), Const(1.0f))
    }
    show(t4)
    println("term5")
    val t5 = reset {
      Assign(Snd(trans(term5)), Const(1.0f))
    }
    show(t5)
  }
}

