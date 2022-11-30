package io.univalence.stackoverflow



import io.univalence.stackoverflow.Path.Root

import language.experimental.macros
import magnolia1._

import scala.reflect.ClassTag
import scala.reflect.runtime.universe
import scala.util.Try


case class Transformed[V,W](result: V, warnings: Seq[W]) {
  def map[B](f: V => B):Transformed[B,W] = Transformed(f(result), warnings)
}

sealed trait Path {

  def depth:Int = getParent.map(_.depth +1).getOrElse(0)

  def getParent:Option[Path] =
    this match {
      case Path.Root => None
      case Path.Field(p, _) => Some(p)
      case Path.Optional(p) => Some(p)
      case Path.Sequential(p) => Some(p)
    }
}

object Path {
  case object Root extends Path
  case class Field(parent:Path, name:String) extends Path
  case class Optional(parent:Path) extends Path
  case class Sequential(parent:Path) extends Path
}

object UpdateGeneric {


  class On[X] {
    def updateSome[V:Updater.ToTraverse](value:V):UpdateSome[V] = new UpdateSome[V] {
      override def using[W](tx: (Path, X) => Either[W, X]): Transformed[V, W] = {
        implicitly[Updater.ToTraverse[V]].using(value,tx, Path.Root)
      }
    }

    trait UpdateSome[V] {
        def using[W](tx: (Path, X) => Either[W, X]): Transformed[V,W]
    }

    sealed trait Updater[V]

    trait UpdaterLowPriority2 {
      implicit def toSkip[V]: Updater.ToSkip[V] = new Updater.ToSkip
    }

    trait UpdaterLowPriority1 extends UpdaterLowPriority2 {
      implicit def opt[V](implicit updater: Updater[V]):Updater.ToTraverse[Option[V]] = new Updater.ToTraverse[Option[V]] {
        override def using[W](v: Option[V], tx: (Path, X) => Either[W, X], base:Path): Transformed[Option[V], W] = {
          v match {
            case None => Transformed(None, Nil)
            case Some(vv) =>
              updater match {
                case tt:Updater.ToTraverse[V] => tt.using(vv,tx, Path.Optional(base) ).map(x => Some(x))
                case _ => Transformed(v, Nil)
              }
          }
        }
      }

      implicit def seq[V](implicit updater: Updater[V]):Updater.ToTraverse[Seq[V]] = new Updater.ToTraverse[Seq[V]] {
        override def using[W](v: Seq[V], tx: (Path, X) => Either[W, X], base: Path): Transformed[Seq[V], W] = {

          updater match {
            case tt:Updater.ToTraverse[V] =>
              val vs = v.map(v => tt.using(v,tx, Path.Sequential(base)))
              Transformed(vs.map(_.result), vs.flatMap(_.warnings))
            case _ => Transformed(v, Nil)
          }

        }
      }
    }

    object Updater extends UpdaterLowPriority1 {

      implicit case object ToUpdate extends Updater[X]

      class ToSkip[V] extends Updater[V]


      trait ToTraverse[V] extends Updater[V] {
        def using[W](v:V , tx: (Path, X) => Either[W, X], base:Path): Transformed[V,W]
      }

      type Typeclass[T] = Updater[T]

      def join[T](ctx: CaseClass[Typeclass, T]): Updater.ToTraverse[T] = new Updater.ToTraverse[T] {
        override def using[W](v: T, tx: (Path, X) => Either[W, X], base:Path): Transformed[T, W] = {
          val all = ctx.parameters.map(param =>  {
            param.typeclass match {
              case _:ToSkip[_] => Transformed(param.dereference(v), Nil)
              case tt:ToTraverse[param.PType] =>
                tt.using(param.dereference(v), tx, Path.Field(base, param.label))
              case _ =>
                val x = param.dereference(v).asInstanceOf[X]
                val e: Try[Either[W, X]] = scala.util.Try(tx(Path.Field(base, param.label), x)).recover({ case _: MatchError => Right(x) })
                e.get.fold(w => Transformed(x, List(w)), x => Transformed(x, Nil))
            }
          })
          Transformed(ctx.rawConstruct(all.map(_.result))  ,all.flatMap(_.warnings))
        }
      }

      implicit def gen[T]: Updater.ToTraverse[T] = macro Magnolia.gen[T]
    }
  }

  def on[X]:On[X] = new On
}


object UpdateGenericWithReflexion {
  import scala.reflect.runtime.universe._

  class On[X:TypeTag] {
    trait UpdateSome[V] {
      def using[W](tx: (Path, X) => Either[W, X]): Transformed[V,W]
    }

    def updateSome[V:TypeTag](v:V):UpdateSome[V] = new UpdateSome[V] {
      override def using[W](tx: (Path, X) => Either[W, X]): Transformed[V, W] = {

        implicit def typeToClassTag[T: TypeTag]: ClassTag[T] = {
          ClassTag[T]( typeTag[T].mirror.runtimeClass( typeTag[T].tpe ) )
        }

        val targetTT = implicitly[TypeTag[X]]
        val mirror = targetTT.mirror

        def transform[VV](vv:VV, tpe:universe.Type):Transformed[VV, W] = {
          implicit val ict: ClassTag[VV] = ClassTag[VV](mirror.runtimeClass(tpe))
          //val tpe: universe.Type = tt.tpe

          val constructor: Option[universe.MethodSymbol] = tpe.members.collectFirst({
            case s: MethodSymbol if s.isConstructor => s
          })

          constructor match {
            case None => Transformed(vv, Nil)
            case _ if !tpe.typeSymbol.asClass.isCaseClass => Transformed(vv, Nil)
            case Some(constructor)  =>
              val const: universe.MethodMirror = mirror.reflectClass(tpe.typeSymbol.asClass).reflectConstructor(constructor)
              val names = constructor.paramLists.head.map(_.name.toString)

              val fields = tpe.members.collect({
                case f: MethodSymbol if f.isCaseAccessor => f
              }).toSeq.sortBy(m => {
                val name = m.name.toString
                names.indexOf(name)
              })

              val reflectedV: universe.InstanceMirror = mirror.reflect(vv)

              val transformedFields: Seq[Transformed[Any, W]] = fields.map(f => {
                val rt: universe.Type = f.returnType
                val x = reflectedV.reflectMethod(f)()
                if (rt =:= targetTT.tpe) {
                  scala.util.Try(tx(Root, x.asInstanceOf[X])).recover({ case _: MatchError => Right(x) }).get.fold(w =>
                    Transformed(x, Seq(w)), x => Transformed(x, Nil))
                } else {
                  if(rt <:< typeOf[Option[Any]]) {
                    if(rt.typeArgs.head.typeSymbol.asClass.isCaseClass) {
                      x.asInstanceOf[Option[Any]] match {
                        case None => Transformed(None, Nil)
                        case Some(x) => transform(x, rt.typeArgs.head).map(x => Some(x))
                      }
                    } else {
                      Transformed(x, Nil)
                    }
                  } else if (rt <:< typeOf[Seq[Any]]) {
                    if(rt.typeArgs.head.typeSymbol.asClass.isCaseClass) {
                     val seq =  x.asInstanceOf[Seq[Any]].map(x => transform(x, rt.typeArgs.head))
                      Transformed(seq.map(_.result), seq.flatMap(_.warnings))
                    } else {
                      Transformed(x, Nil)
                    }
                  } else if (rt.typeSymbol.asClass.isCaseClass) {
                    transform(x, rt)
                  } else {
                    Transformed(x, Nil)
                  }
                }
              })

              val newNewV = const(transformedFields.map(_.result): _*).asInstanceOf[VV]
              Transformed(newNewV, transformedFields.flatMap(_.warnings))
          }
        }

        transform(v, implicitly[TypeTag[V]].tpe)
      }
    }
  }


  def on[X:Manifest]:On[X] = new On[X]

}




case class SomeObjectA(toto:Option[String], titi:Int, tata: Option[Int], inner:Option[SomeObjectB])

case class SomeObjectB(tutu:Option[String])

case class SomeObjectC(b1:SomeObjectB, as:Seq[SomeObjectA])

object Objects {


  val b: SomeObjectB = SomeObjectB(Some("tutu"))
  val a: SomeObjectA = SomeObjectA(Some("toto"), 0, Some(1), Some(b))
  val c: SomeObjectC = SomeObjectC(b, Seq(a))


  object OptionStringToNone {
    val b: SomeObjectB = SomeObjectB(None)
    val a: SomeObjectA = SomeObjectA(None, 0, Some(1), Some(b))
    val c: SomeObjectC = SomeObjectC(b, Seq(a))
  }

}



/**
 * Todo
 * * check the Path construction
 *
 */
object TestSyntaxManifest {


  import Objects._

  private val plop: UpdateGenericWithReflexion.On[Option[String]] = UpdateGenericWithReflexion.on[Option[String]]

  private val res3 = plop.updateSome(c).using((_, _) => Right(None))

  private val res2 = plop.updateSome(a).using((_, _) => Right(None))
  private  val res = plop.updateSome(b).using((p, x) => Right(None))

  def main(args: Array[String]): Unit = {
    assert(res.result == b.copy(None))
    assert(res2.result == a.copy(None, inner = a.inner.map(_.copy(None))))
    assert(res3.result == OptionStringToNone.c)
  }

}

object TestSyntax {

  import Objects._

  private val opt: UpdateGeneric.On[Option[String]] = UpdateGeneric.on[Option[String]]



  def main(args: Array[String]): Unit = {
    val a2: SomeObjectA = opt.updateSome(a).using((_,_) => Right(None)).result

    assert(a2 == a.copy(None, inner = a.inner.map(_.copy(None))))

    val result = opt.updateSome(a).using({
      case (path, _) if path.depth < 2 => Right(None)
    }).result

    assert(result == a.copy(None))


   // implicit val bTrv = opt.Updater.gen[SomeObjectB]
    val result1 = opt.updateSome(c).using((_, _) => Right(None)).result
    assert(result1 == OptionStringToNone.c)


  }
}





