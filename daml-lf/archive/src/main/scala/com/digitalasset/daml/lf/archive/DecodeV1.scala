// Copyright (c) 2019 The DAML Authors. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

package com.digitalasset.daml.lf
package archive

import java.util

import com.digitalasset.daml.lf.archive.Decode.ParseError
import com.digitalasset.daml.lf.data.Ref._
import com.digitalasset.daml.lf.data.{Decimal, ImmArray, Numeric, Time}
import ImmArray.ImmArraySeq
import com.digitalasset.daml.lf.language.Ast._
import com.digitalasset.daml.lf.language.Util._
import com.digitalasset.daml.lf.language.{LanguageVersion => LV}
import com.digitalasset.daml_lf.{DamlLf1 => PLF}
import com.google.protobuf.CodedInputStream

import scala.annotation.tailrec
import scala.collection.JavaConverters._
import scala.collection.{breakOut, mutable}

private[archive] class DecodeV1(minor: LV.Minor) extends Decode.OfPackage[PLF.Package] {

  import Decode._, DecodeV1._

  private val languageVersion = LV(LV.Major.V1, minor)

  override def decodePackage(
      packageId: PackageId,
      lfPackage: PLF.Package,
      onlySerializableDataDefs: Boolean
  ): Package = {
    val internedStrings: ImmArraySeq[String] = ImmArraySeq(
      lfPackage.getInternedStringsList.asScala: _*)
    if (internedStrings.nonEmpty)
      assertSince(LV.Features.internedPackageId, "interned strings table")

    val internedDottedNames: ImmArraySeq[DottedName] =
      decodeInternedDottedNames(lfPackage.getInternedDottedNamesList.asScala, internedStrings)

    Package(
      lfPackage.getModulesList.asScala
        .map(
          ModuleDecoder(
            packageId,
            internedStrings,
            internedDottedNames,
            _,
            onlySerializableDataDefs).decode))
  }

  type ProtoModule = PLF.Module

  override def protoModule(cis: CodedInputStream): ProtoModule =
    PLF.Module.parser().parseFrom(cis)

  override def decodeScenarioModule(packageId: PackageId, lfModule: ProtoModule): Module =
    ModuleDecoder(
      packageId,
      ImmArraySeq.empty,
      ImmArraySeq.empty,
      lfModule,
      onlySerializableDataDefs = false).decode()

  private[this] def decodeInternedDottedNames(
      internedList: Seq[PLF.InternedDottedName],
      internedStrings: ImmArraySeq[String]): ImmArraySeq[DottedName] = {
    if (internedList.nonEmpty)
      assertSince(LV.Features.internedDottedNames, "interned dotted names table")

    def outOfRange(id: Int) =
      ParseError(s"invalid string table index $id")

    internedList
      .map(
        idn =>
          decodeSegments(
            idn.getSegmentIdsList.asScala
              .map(id => internedStrings.lift(id).getOrElse(throw outOfRange(id)))(breakOut))
      )(breakOut)
  }

  private[this] def decodeSegments(segments: ImmArray[String]): DottedName =
    DottedName.fromSegments(segments.toSeq) match {
      case Left(err) => throw new ParseError(err)
      case Right(x) => x
    }

  case class ModuleDecoder(
      packageId: PackageId,
      internedStrings: ImmArraySeq[String],
      internedDottedNames: ImmArraySeq[DottedName],
      lfModule: PLF.Module,
      onlySerializableDataDefs: Boolean
  ) {

    val moduleName: ModuleName =
      decodeDottedName(lfModule.getName)

    private var currentDefinitionRef: Option[DefinitionRef] = None

    def decode(): Module = {
      val defs = mutable.ArrayBuffer[(DottedName, Definition)]()
      val templates = mutable.ArrayBuffer[(DottedName, Template)]()

      // collect data types
      lfModule.getDataTypesList.asScala
        .filter(!onlySerializableDataDefs || _.getSerializable)
        .foreach { defn =>
          val defName = decodeDottedName(defn.getName)
          currentDefinitionRef = Some(DefinitionRef(packageId, QualifiedName(moduleName, defName)))
          val d = decodeDefDataType(defn)
          defs += (defName -> d)
        }

      if (!onlySerializableDataDefs) {
        // collect values
        lfModule.getValuesList.asScala.foreach { defn =>
          val nameWithType = defn.getNameWithType
          val defName =
            handleInternedDottedName(
              nameWithType.getNameList,
              nameWithType.getNameInternedDottedName,
              "NameWithType.name"
            )
          currentDefinitionRef = Some(DefinitionRef(packageId, QualifiedName(moduleName, defName)))
          val d = decodeDefValue(defn)
          defs += (defName -> d)
        }
      }

      // collect templates
      lfModule.getTemplatesList.asScala.foreach { defn =>
        val defName = decodeDottedName(defn.getTycon)
        currentDefinitionRef = Some(DefinitionRef(packageId, QualifiedName(moduleName, defName)))
        templates += ((defName, decodeTemplate(defn)))
      }

      Module(moduleName, defs, templates, languageVersion, decodeFeatureFlags(lfModule.getFlags))
    }

    // -----------------------------------------------------------------------
    private[this] def getInternedString(id: Int) =
      internedStrings.lift(id).getOrElse {
        throw ParseError(s"invalid internedString table index $id")
      }

    private[this] def getInternedPackageId(id: Int): PackageId = {
      assertSince(LV.Features.internedPackageId, "interned PackageId")
      eitherToParseError(PackageId.fromString(getInternedString(id)))
    }

    private[this] def getInternedName(id: Int, description: => String): Name = {
      assertSince(LV.Features.internedStrings, description)
      eitherToParseError(Name.fromString(getInternedString(id)))
    }

    private[this] def getInternedDottedName(id: Int): DottedName =
      internedDottedNames.lift(id).getOrElse {
        assertSince(LV.Features.internedDottedNames, "interned DottedNames")
        throw ParseError(s"invalid dotted name table index $id")
      }

    private[this] def decodeDottedName(name: PLF.DottedName): DottedName =
      if (name.getSegmentsCount == 0) {
        getInternedDottedName(name.getSegmentsInternedString)
      } else {
        decodeSegments(ImmArray(name.getSegmentsList.asScala))
      }

    private[this] def decodeFeatureFlags(flags: PLF.FeatureFlags): FeatureFlags = {
      // NOTE(JM, #157): We disallow loading packages with these flags because they impact the Ledger API in
      // ways that would currently make it quite complicated to support them.
      if (!flags.getDontDivulgeContractIdsInCreateArguments || !flags.getDontDiscloseNonConsumingChoicesToObservers) {
        throw new ParseError("Deprecated feature flag settings detected, refusing to parse package")
      }
      FeatureFlags(
        forbidPartyLiterals = flags.getForbidPartyLiterals
      )
    }

    private[this] def decodeDefDataType(lfDataType: PLF.DefDataType): DDataType = {
      val params = ImmArray(lfDataType.getParamsList.asScala).map(decodeTypeVarWithKind)
      DDataType(
        lfDataType.getSerializable,
        params,
        lfDataType.getDataConsCase match {
          case PLF.DefDataType.DataConsCase.RECORD =>
            DataRecord(decodeFields(ImmArray(lfDataType.getRecord.getFieldsList.asScala)), None)
          case PLF.DefDataType.DataConsCase.VARIANT =>
            DataVariant(decodeFields(ImmArray(lfDataType.getVariant.getFieldsList.asScala)))
          case PLF.DefDataType.DataConsCase.ENUM =>
            assertSince(LV.Features.enum, "DefDataType.DataCons.Enum")
            assertEmpty(params.toSeq, "params")
            DataEnum(decodeEnumCon(lfDataType.getEnum))
          case PLF.DefDataType.DataConsCase.DATACONS_NOT_SET =>
            throw ParseError("DefDataType.DATACONS_NOT_SET")

        }
      )
    }

    def handleInternedString(string: String, stringId: Int, description: => String) =
      if (versionIsOlderThan(LV.Features.internedStrings)) {
        assertZero(stringId, description + "_interned_string")
        string
      } else {
        assertEmpty(string, description)
        internedStrings(stringId)
      }

    def handleInternedName(string: String, stringId: Int, description: => String) =
      toName(handleInternedString(string, stringId, description))

    def handleInternedNames(
        strings: util.List[String],
        stringIds: util.List[Integer],
        description: => String): Seq[Name] =
      if (versionIsOlderThan(LV.Features.internedStrings)) {
        assertEmpty(stringIds, description + "_interned_string")
        strings.asScala.map(toName)
      } else {
        assertEmpty(strings, description)
        stringIds.asScala.map(id => toName(internedStrings(id)))
      }

    def handleInternedDottedName(
        strings: util.List[String],
        id: Int,
        description: => String): DottedName =
      if (versionIsOlderThan(LV.Features.internedDottedNames)) {
        assertZero(id, description + "_interned_dotted_name")
        decodeSegments(ImmArray(strings.asScala))
      } else {
        assertEmpty(strings, description)
        internedDottedNames(id)
      }

    private[this] def decodeFieldWithType(lfFieldWithType: PLF.FieldWithType): (Name, Type) =
      handleInternedName(
        lfFieldWithType.getField,
        lfFieldWithType.getFieldInternedString,
        "FieldWithType.name",
      ) -> decodeType(lfFieldWithType.getType)

    private[this] def decodeFields(lfFields: ImmArray[PLF.FieldWithType]): ImmArray[(Name, Type)] =
      lfFields.map(decodeFieldWithType)

    private[this] def decodeFieldWithExpr(
        lfFieldWithExpr: PLF.FieldWithExpr,
        definition: String
    ): (Name, Expr) =
      handleInternedName(
        lfFieldWithExpr.getField,
        lfFieldWithExpr.getFieldInternedString,
        "FieldWithType.name",
      ) -> decodeExpr(lfFieldWithExpr.getExpr, definition)

    private[this] def decodeEnumCon(
        enumCon: PLF.DefDataType.EnumConstructors): ImmArray[EnumConName] =
      ImmArray(
        handleInternedNames(
          enumCon.getConstructorsList,
          enumCon.getConstructorsInternedStringsList,
          "EnumConstructors.constructors"
        ))

    private[this] def decodeDefValue(lfValue: PLF.DefValue): DValue = {
      val name = handleInternedDottedName(
        lfValue.getNameWithType.getNameList,
        lfValue.getNameWithType.getNameInternedDottedName,
        "DefValue.NameWithType.name"
      )
      DValue(
        typ = decodeType(lfValue.getNameWithType.getType),
        noPartyLiterals = lfValue.getNoPartyLiterals,
        body = decodeExpr(lfValue.getExpr, name.toString),
        isTest = lfValue.getIsTest
      )
    }

    private def decodeLocation(lfExpr: PLF.Expr, definition: String): Option[Location] =
      if (lfExpr.hasLocation && lfExpr.getLocation.hasRange) {
        val loc = lfExpr.getLocation
        val (pkgId, module) =
          if (loc.hasModule)
            decodeModuleRef(loc.getModule)
          else
            (packageId, moduleName)

        val range = loc.getRange
        Some(
          Location(
            pkgId,
            module,
            definition,
            (range.getStartLine, range.getStartCol),
            (range.getEndLine, range.getEndCol)))
      } else {
        None
      }

    private[this] def decodeTemplateKey(
        tpl: DottedName,
        key: PLF.DefTemplate.DefKey,
        tplVar: ExprVarName): TemplateKey = {
      assertSince(LV.Features.contractKeys, "DefTemplate.DefKey")
      val keyExpr = key.getKeyExprCase match {
        case PLF.DefTemplate.DefKey.KeyExprCase.KEY =>
          decodeKeyExpr(key.getKey, tplVar)
        case PLF.DefTemplate.DefKey.KeyExprCase.COMPLEX_KEY => {
          assertSince(LV.Features.complexContactKeys, "DefTemplate.DefKey.complex_key")
          decodeExpr(key.getComplexKey, s"${tpl}:key")
        }
        case PLF.DefTemplate.DefKey.KeyExprCase.KEYEXPR_NOT_SET =>
          throw ParseError("DefKey.KEYEXPR_NOT_SET")
      }
      TemplateKey(
        decodeType(key.getType),
        keyExpr,
        maintainers = decodeExpr(key.getMaintainers, s"${tpl}:maintainer")
      )
    }

    private[this] def decodeKeyExpr(expr: PLF.KeyExpr, tplVar: ExprVarName): Expr = {
      expr.getSumCase match {
        case PLF.KeyExpr.SumCase.RECORD =>
          val recCon = expr.getRecord
          ERecCon(
            tycon = decodeTypeConApp(recCon.getTycon),
            fields = ImmArray(recCon.getFieldsList.asScala).map(
              field =>
                handleInternedName(
                  field.getField,
                  field.getFieldInternedString,
                  "KeyExpr.field"
                ) -> decodeKeyExpr(field.getExpr, tplVar))
          )

        case PLF.KeyExpr.SumCase.PROJECTIONS =>
          val lfProjs = expr.getProjections.getProjectionsList.asScala
          lfProjs.foldLeft(EVar(tplVar): Expr)(
            (acc, lfProj) =>
              ERecProj(
                decodeTypeConApp(lfProj.getTycon),
                handleInternedName(
                  lfProj.getField,
                  lfProj.getFieldInternedString,
                  "KeyExpr.Projection.field"),
                acc
            ))

        case PLF.KeyExpr.SumCase.SUM_NOT_SET =>
          throw ParseError("KeyExpr.SUM_NOT_SET")
      }
    }

    private[this] def decodeTemplate(lfTempl: PLF.DefTemplate): Template = {
      val tpl = decodeDottedName(lfTempl.getTycon)
      val paramName = handleInternedName(
        lfTempl.getParam,
        lfTempl.getParamInternedString,
        "DefTemplate.param"
      )
      Template(
        param = paramName,
        precond = if (lfTempl.hasPrecond) decodeExpr(lfTempl.getPrecond, s"$tpl:ensure") else ETrue,
        signatories = decodeExpr(lfTempl.getSignatories, s"$tpl.signatory"),
        agreementText = decodeExpr(lfTempl.getAgreement, s"$tpl:agreement"),
        choices = lfTempl.getChoicesList.asScala
          .map(decodeChoice(tpl, _))
          .map(ch => (ch.name, ch)),
        observers = decodeExpr(lfTempl.getObservers, s"$tpl:observer"),
        key =
          if (lfTempl.hasKey) Some(decodeTemplateKey(tpl, lfTempl.getKey, paramName))
          else None
      )
    }

    private[this] def decodeChoice(
        tpl: DottedName,
        lfChoice: PLF.TemplateChoice): TemplateChoice = {
      val (v, t) = decodeBinder(lfChoice.getArgBinder)
      val chName = handleInternedName(
        lfChoice.getName,
        lfChoice.getNameInternedString,
        "TemplateChoice.name"
      )
      val selfBinder = handleInternedName(
        lfChoice.getSelfBinder,
        lfChoice.getSelfBinderInternedString,
        "TemplateChoice.self_binder"
      )
      TemplateChoice(
        name = chName,
        consuming = lfChoice.getConsuming,
        controllers = decodeExpr(lfChoice.getControllers, s"$tpl:$chName:controller"),
        selfBinder = selfBinder,
        argBinder = Some(v) -> t,
        returnType = decodeType(lfChoice.getRetType),
        update = decodeExpr(lfChoice.getUpdate, s"$tpl:$chName:choice")
      )
    }

    private[lf] def decodeKind(lfKind: PLF.Kind): Kind =
      lfKind.getSumCase match {
        case PLF.Kind.SumCase.STAR => KStar
        case PLF.Kind.SumCase.NAT =>
          assertSince(LV.Features.numeric, "Kind.NAT")
          KNat
        case PLF.Kind.SumCase.ARROW =>
          val kArrow = lfKind.getArrow
          val params = kArrow.getParamsList.asScala
          assertNonEmpty(params, "params")
          (params :\ decodeKind(kArrow.getResult))((param, kind) => KArrow(decodeKind(param), kind))
        case PLF.Kind.SumCase.SUM_NOT_SET =>
          throw ParseError("Kind.SUM_NOT_SET")
      }

    private[lf] def decodeType(lfType: PLF.Type): Type =
      lfType.getSumCase match {
        case PLF.Type.SumCase.VAR =>
          val tvar = lfType.getVar
          val varName = handleInternedName(
            tvar.getVar,
            tvar.getVarInternedString,
            "Type.var.name"
          )
          tvar.getArgsList.asScala
            .foldLeft[Type](TVar(varName))((typ, arg) => TApp(typ, decodeType(arg)))
        case PLF.Type.SumCase.NAT =>
          assertSince(LV.Features.numeric, "Type.NAT")
          Numeric.Scale
            .fromLong(lfType.getNat)
            .fold[TNat](
              _ =>
                throw ParseError(
                  s"TNat must be between ${Numeric.Scale.MinValue} and ${Numeric.Scale.MaxValue}, found ${lfType.getNat}"),
              TNat
            )
        case PLF.Type.SumCase.CON =>
          val tcon = lfType.getCon
          (TTyCon(decodeTypeConName(tcon.getTycon)) /: [Type] tcon.getArgsList.asScala)(
            (typ, arg) => TApp(typ, decodeType(arg)))
        case PLF.Type.SumCase.PRIM =>
          val prim = lfType.getPrim
          val baseType =
            if (prim.getPrim == PLF.PrimType.DECIMAL) {
              assertUntil(LV.Features.numeric, "PrimType.DECIMAL")
              TDecimal
            } else {
              val info = builtinTypeInfoMap(prim.getPrim)
              assertSince(info.minVersion, prim.getPrim.getValueDescriptor.getFullName)
              TBuiltin(info.bTyp)
            }
          (baseType /: [Type] prim.getArgsList.asScala)((typ, arg) => TApp(typ, decodeType(arg)))
        case PLF.Type.SumCase.FUN =>
          assertUntil(LV.Features.arrowType, "Type.Fun")
          val tFun = lfType.getFun
          val params = tFun.getParamsList.asScala
          assertNonEmpty(params, "params")
          (params :\ decodeType(tFun.getResult))((param, res) => TFun(decodeType(param), res))
        case PLF.Type.SumCase.FORALL =>
          val tForall = lfType.getForall
          val vars = tForall.getVarsList.asScala
          assertNonEmpty(vars, "vars")
          (vars :\ decodeType(tForall.getBody))((binder, acc) =>
            TForall(decodeTypeVarWithKind(binder), acc))
        case PLF.Type.SumCase.TUPLE =>
          val tuple = lfType.getTuple
          val fields = tuple.getFieldsList.asScala
          assertNonEmpty(fields, "fields")
          TTuple(fields.map(decodeFieldWithType)(breakOut))

        case PLF.Type.SumCase.SUM_NOT_SET =>
          throw ParseError("Type.SUM_NOT_SET")
      }

    private[this] def decodeModuleRef(lfRef: PLF.ModuleRef): (PackageId, ModuleName) = {
      val modName = decodeDottedName(lfRef.getModuleName)
      import PLF.PackageRef.{SumCase => SC}

      val pkgId = lfRef.getPackageRef.getSumCase match {
        case SC.SELF =>
          this.packageId
        case SC.PACKAGE_ID =>
          toPackageId(lfRef.getPackageRef.getPackageId, "PackageRef.packageId")
        case SC.PACKAGE_ID_INTERNED_STRING =>
          getInternedPackageId(lfRef.getPackageRef.getPackageIdInternedString)
        case SC.SUM_NOT_SET =>
          throw ParseError("PackageRef.SUM_NOT_SET")
      }
      (pkgId, modName)
    }

    private[this] def decodeValName(lfVal: PLF.ValName): ValueRef = {
      val (packageId, module) = decodeModuleRef(lfVal.getModule)
      val name: DottedName = handleInternedDottedName(
        lfVal.getNameList,
        lfVal.getNameInternedDottedName,
        "ValName.name"
      )
      ValueRef(packageId, QualifiedName(module, name))
    }

    private[this] def decodeTypeConName(lfTyConName: PLF.TypeConName): TypeConName = {
      val (packageId, module) = decodeModuleRef(lfTyConName.getModule)
      val name = decodeDottedName(lfTyConName.getName)
      Identifier(packageId, QualifiedName(module, name))
    }

    private[this] def decodeTypeConApp(lfTyConApp: PLF.Type.Con): TypeConApp =
      TypeConApp(
        decodeTypeConName(lfTyConApp.getTycon),
        ImmArray(lfTyConApp.getArgsList.asScala.map(decodeType))
      )

    private[lf] def decodeExpr(lfExpr: PLF.Expr, definition: String): Expr =
      decodeLocation(lfExpr, definition) match {
        case None => decodeExprBody(lfExpr, definition)
        case Some(loc) => ELocation(loc, decodeExprBody(lfExpr, definition))
      }

    private[this] def decodeExprBody(lfExpr: PLF.Expr, definition: String): Expr =
      lfExpr.getSumCase match {
        case PLF.Expr.SumCase.VAR =>
          assertUntil(LV.Features.internedStrings, "Expr.var")
          EVar(toName(lfExpr.getVar))

        case PLF.Expr.SumCase.VAR_INTERNED_STRING =>
          EVar(getInternedName(lfExpr.getVarInternedString, "Expr.var_interned_id"))

        case PLF.Expr.SumCase.VAL =>
          EVal(decodeValName(lfExpr.getVal))

        case PLF.Expr.SumCase.PRIM_LIT =>
          EPrimLit(decodePrimLit(lfExpr.getPrimLit))

        case PLF.Expr.SumCase.PRIM_CON =>
          lfExpr.getPrimCon match {
            case PLF.PrimCon.CON_UNIT => EUnit
            case PLF.PrimCon.CON_FALSE => EFalse
            case PLF.PrimCon.CON_TRUE => ETrue
            case PLF.PrimCon.UNRECOGNIZED =>
              throw ParseError("PrimCon.UNRECOGNIZED")
          }

        case PLF.Expr.SumCase.BUILTIN =>
          val info = DecodeV1.builtinInfoMap(lfExpr.getBuiltin)
          assertSince(info.minVersion, lfExpr.getBuiltin.getValueDescriptor.getFullName)
          info.maxVersion.foreach(assertUntil(_, lfExpr.getBuiltin.getValueDescriptor.getFullName))
          ntimes[Expr](
            info.implicitDecimalScaleParameters,
            ETyApp(_, TDecimalScale),
            EBuiltin(info.builtin))

        case PLF.Expr.SumCase.REC_CON =>
          val recCon = lfExpr.getRecCon
          ERecCon(
            tycon = decodeTypeConApp(recCon.getTycon),
            fields = ImmArray(recCon.getFieldsList.asScala).map(decodeFieldWithExpr(_, definition))
          )

        case PLF.Expr.SumCase.REC_PROJ =>
          val recProj = lfExpr.getRecProj
          ERecProj(
            tycon = decodeTypeConApp(recProj.getTycon),
            field = handleInternedName(
              recProj.getField,
              recProj.getFieldInternedString,
              "Expr.RecProj.name"
            ),
            record = decodeExpr(recProj.getRecord, definition)
          )

        case PLF.Expr.SumCase.REC_UPD =>
          val recUpd = lfExpr.getRecUpd
          ERecUpd(
            tycon = decodeTypeConApp(recUpd.getTycon),
            field = handleInternedName(
              recUpd.getField,
              recUpd.getFieldInternedString,
              "Expr.RecUpd.field"
            ),
            record = decodeExpr(recUpd.getRecord, definition),
            update = decodeExpr(recUpd.getUpdate, definition)
          )

        case PLF.Expr.SumCase.VARIANT_CON =>
          val varCon = lfExpr.getVariantCon
          EVariantCon(
            decodeTypeConApp(varCon.getTycon),
            handleInternedName(
              varCon.getVariantCon,
              varCon.getVariantConInternedString,
              "Expr.VariantCon.variant_con"
            ),
            decodeExpr(varCon.getVariantArg, definition)
          )

        case PLF.Expr.SumCase.ENUM_CON =>
          assertSince(LV.Features.enum, "Expr.Enum")
          val enumCon = lfExpr.getEnumCon
          EEnumCon(
            decodeTypeConName(enumCon.getTycon),
            handleInternedName(
              enumCon.getEnumCon,
              enumCon.getEnumConInternedString,
              "Expr.EnumCon.enum_con")
          )

        case PLF.Expr.SumCase.TUPLE_CON =>
          val tupleCon = lfExpr.getTupleCon
          ETupleCon(
            ImmArray(tupleCon.getFieldsList.asScala).map(decodeFieldWithExpr(_, definition))
          )

        case PLF.Expr.SumCase.TUPLE_PROJ =>
          val tupleProj = lfExpr.getTupleProj
          ETupleProj(
            field = handleInternedName(
              tupleProj.getField,
              tupleProj.getFieldInternedString,
              "Expr.TupleProj.field"
            ),
            tuple = decodeExpr(tupleProj.getTuple, definition)
          )

        case PLF.Expr.SumCase.TUPLE_UPD =>
          val tupleUpd = lfExpr.getTupleUpd
          ETupleUpd(
            field = handleInternedName(
              tupleUpd.getField,
              tupleUpd.getFieldInternedString,
              "Expr.TupleUpd.field"
            ),
            tuple = decodeExpr(tupleUpd.getTuple, definition),
            update = decodeExpr(tupleUpd.getUpdate, definition)
          )

        case PLF.Expr.SumCase.APP =>
          val app = lfExpr.getApp
          val args = app.getArgsList.asScala
          assertNonEmpty(args, "args")
          (decodeExpr(app.getFun, definition) /: args)((e, arg) =>
            EApp(e, decodeExpr(arg, definition)))

        case PLF.Expr.SumCase.ABS =>
          val lfAbs = lfExpr.getAbs
          val params = lfAbs.getParamList.asScala
          assertNonEmpty(params, "params")
          // val params = lfAbs.getParamList.asScala.map(decodeBinder)
          (params :\ decodeExpr(lfAbs.getBody, definition))((param, e) =>
            EAbs(decodeBinder(param), e, currentDefinitionRef))

        case PLF.Expr.SumCase.TY_APP =>
          val tyapp = lfExpr.getTyApp
          val args = tyapp.getTypesList.asScala
          assertNonEmpty(args, "args")
          (decodeExpr(tyapp.getExpr, definition) /: args)((e, arg) => ETyApp(e, decodeType(arg)))

        case PLF.Expr.SumCase.TY_ABS =>
          val lfTyAbs = lfExpr.getTyAbs
          val params = lfTyAbs.getParamList.asScala
          assertNonEmpty(params, "params")
          (params :\ decodeExpr(lfTyAbs.getBody, definition))((param, e) =>
            ETyAbs(decodeTypeVarWithKind(param), e))

        case PLF.Expr.SumCase.LET =>
          val lfLet = lfExpr.getLet
          val bindings = lfLet.getBindingsList.asScala
          assertNonEmpty(bindings, "bindings")
          (bindings :\ decodeExpr(lfLet.getBody, definition))((binding, e) => {
            val (v, t) = decodeBinder(binding.getBinder)
            ELet(Binding(Some(v), t, decodeExpr(binding.getBound, definition)), e)
          })

        case PLF.Expr.SumCase.NIL =>
          ENil(decodeType(lfExpr.getNil.getType))

        case PLF.Expr.SumCase.CONS =>
          val cons = lfExpr.getCons
          val front = cons.getFrontList.asScala
          assertNonEmpty(front, "front")
          val typ = decodeType(cons.getType)
          ECons(
            typ,
            ImmArray(front.map(decodeExpr(_, definition))),
            decodeExpr(cons.getTail, definition))

        case PLF.Expr.SumCase.CASE =>
          val case_ = lfExpr.getCase
          ECase(
            decodeExpr(case_.getScrut, definition),
            ImmArray(case_.getAltsList.asScala).map(decodeCaseAlt(_, definition))
          )

        case PLF.Expr.SumCase.UPDATE =>
          EUpdate(decodeUpdate(lfExpr.getUpdate, definition))

        case PLF.Expr.SumCase.SCENARIO =>
          EScenario(decodeScenario(lfExpr.getScenario, definition))

        case PLF.Expr.SumCase.OPTIONAL_NONE =>
          assertSince(LV.Features.optional, "Expr.OptionalNone")
          ENone(decodeType(lfExpr.getOptionalNone.getType))

        case PLF.Expr.SumCase.OPTIONAL_SOME =>
          assertSince(LV.Features.optional, "Expr.OptionalSome")
          val some = lfExpr.getOptionalSome
          ESome(decodeType(some.getType), decodeExpr(some.getBody, definition))

        case PLF.Expr.SumCase.TO_ANY =>
          assertSince(LV.Features.anyTemplate, "Expr.ToAnyTemplate")
          decodeType(lfExpr.getToAny.getType) match {
            case TTyCon(tmplId) =>
              EToAnyTemplate(
                tmplId = tmplId,
                body = decodeExpr(lfExpr.getToAny.getExpr, definition))
            case ty => throw ParseError(s"TO_ANY must be applied to a template type but got $ty")
          }

        case PLF.Expr.SumCase.FROM_ANY =>
          assertSince(LV.Features.anyTemplate, "Expr.FromAnyTemplate")
          val fromAny = lfExpr.getFromAny
          decodeType(fromAny.getType) match {
            case TTyCon(tmplId) =>
              EFromAnyTemplate(tmplId = tmplId, body = decodeExpr(fromAny.getExpr, definition))
            case ty => throw ParseError(s"FROM_ANY must be applied to a template type but got $ty")
          }

        case PLF.Expr.SumCase.SUM_NOT_SET =>
          throw ParseError("Expr.SUM_NOT_SET")
      }

    private[this] def decodeCaseAlt(lfCaseAlt: PLF.CaseAlt, definition: String): CaseAlt = {
      val pat: CasePat = lfCaseAlt.getSumCase match {
        case PLF.CaseAlt.SumCase.DEFAULT =>
          CPDefault
        case PLF.CaseAlt.SumCase.VARIANT =>
          val variant = lfCaseAlt.getVariant
          CPVariant(
            tycon = decodeTypeConName(variant.getCon),
            variant = handleInternedName(
              variant.getVariant,
              variant.getVariantInternedString,
              "CaseAlt.Variant.variant"
            ),
            binder = handleInternedName(
              variant.getBinder,
              variant.getBinderInternedString,
              "CaseAlt.Variant.binder"
            )
          )
        case PLF.CaseAlt.SumCase.ENUM =>
          assertSince(LV.Features.enum, "CaseAlt.Enum")
          val enum = lfCaseAlt.getEnum
          CPEnum(
            tycon = decodeTypeConName(enum.getCon),
            constructor = handleInternedName(
              enum.getConstructor,
              enum.getConstructorInternedString,
              "CaseAlt.Enum.contructor"
            )
          )
        case PLF.CaseAlt.SumCase.PRIM_CON =>
          CPPrimCon(decodePrimCon(lfCaseAlt.getPrimCon))
        case PLF.CaseAlt.SumCase.NIL =>
          CPNil
        case PLF.CaseAlt.SumCase.CONS =>
          val cons = lfCaseAlt.getCons
          CPCons(
            head = handleInternedName(
              cons.getVarHead,
              cons.getVarHeadInternedString,
              "CaseAlt.Cons.var_head"
            ),
            tail = handleInternedName(
              cons.getVarTail,
              cons.getVarTailInternedString,
              "CaseAlt.Cons.var_tail"
            )
          )

        case PLF.CaseAlt.SumCase.OPTIONAL_NONE =>
          assertSince(LV.Features.optional, "CaseAlt.OptionalNone")
          CPNone

        case PLF.CaseAlt.SumCase.OPTIONAL_SOME =>
          assertSince(LV.Features.optional, "CaseAlt.OptionalSome")
          val some = lfCaseAlt.getOptionalSome
          CPSome(
            handleInternedName(
              some.getVarBody,
              some.getVarBodyInternedString,
              "CaseAlt.OptionalSom.var_body"
            ))

        case PLF.CaseAlt.SumCase.SUM_NOT_SET =>
          throw ParseError("CaseAlt.SUM_NOT_SET")
      }
      CaseAlt(pat, decodeExpr(lfCaseAlt.getBody, definition))
    }

    private[this] def decodeRetrieveByKey(
        value: PLF.Update.RetrieveByKey,
        definition: String): RetrieveByKey = {
      RetrieveByKey(
        decodeTypeConName(value.getTemplate),
        decodeExpr(value.getKey, definition),
      )
    }

    private[this] def decodeUpdate(lfUpdate: PLF.Update, definition: String): Update =
      lfUpdate.getSumCase match {

        case PLF.Update.SumCase.PURE =>
          val pure = lfUpdate.getPure
          UpdatePure(decodeType(pure.getType), decodeExpr(pure.getExpr, definition))

        case PLF.Update.SumCase.BLOCK =>
          val block = lfUpdate.getBlock
          UpdateBlock(
            bindings = ImmArray(block.getBindingsList.asScala.map(decodeBinding(_, definition))),
            body = decodeExpr(block.getBody, definition))

        case PLF.Update.SumCase.CREATE =>
          val create = lfUpdate.getCreate
          UpdateCreate(
            templateId = decodeTypeConName(create.getTemplate),
            arg = decodeExpr(create.getExpr, definition))

        case PLF.Update.SumCase.EXERCISE =>
          val exercise = lfUpdate.getExercise
          UpdateExercise(
            templateId = decodeTypeConName(exercise.getTemplate),
            choice = handleInternedName(
              exercise.getChoice,
              exercise.getChoiceInternedString,
              "Update.Exercise.choice"
            ),
            cidE = decodeExpr(exercise.getCid, definition),
            actorsE =
              if (exercise.hasActor)
                Some(decodeExpr(exercise.getActor, definition))
              else {
                assertSince(LV.Features.optionalExerciseActor, "Update.Exercise.actors optional")
                None
              },
            argE = decodeExpr(exercise.getArg, definition)
          )

        case PLF.Update.SumCase.GET_TIME =>
          UpdateGetTime

        case PLF.Update.SumCase.FETCH =>
          val fetch = lfUpdate.getFetch
          UpdateFetch(
            templateId = decodeTypeConName(fetch.getTemplate),
            contractId = decodeExpr(fetch.getCid, definition))

        case PLF.Update.SumCase.FETCH_BY_KEY =>
          assertSince(LV.Features.contractKeys, "fetchByKey")
          UpdateFetchByKey(decodeRetrieveByKey(lfUpdate.getFetchByKey, definition))

        case PLF.Update.SumCase.LOOKUP_BY_KEY =>
          assertSince(LV.Features.contractKeys, "lookupByKey")
          UpdateLookupByKey(decodeRetrieveByKey(lfUpdate.getLookupByKey, definition))

        case PLF.Update.SumCase.EMBED_EXPR =>
          val embedExpr = lfUpdate.getEmbedExpr
          UpdateEmbedExpr(decodeType(embedExpr.getType), decodeExpr(embedExpr.getBody, definition))

        case PLF.Update.SumCase.SUM_NOT_SET =>
          throw ParseError("Update.SUM_NOT_SET")
      }

    private[this] def decodeScenario(lfScenario: PLF.Scenario, definition: String): Scenario =
      lfScenario.getSumCase match {
        case PLF.Scenario.SumCase.PURE =>
          val pure = lfScenario.getPure
          ScenarioPure(decodeType(pure.getType), decodeExpr(pure.getExpr, definition))

        case PLF.Scenario.SumCase.COMMIT =>
          val commit = lfScenario.getCommit
          ScenarioCommit(
            decodeExpr(commit.getParty, definition),
            decodeExpr(commit.getExpr, definition),
            decodeType(commit.getRetType))

        case PLF.Scenario.SumCase.MUSTFAILAT =>
          val commit = lfScenario.getMustFailAt
          ScenarioMustFailAt(
            decodeExpr(commit.getParty, definition),
            decodeExpr(commit.getExpr, definition),
            decodeType(commit.getRetType))

        case PLF.Scenario.SumCase.BLOCK =>
          val block = lfScenario.getBlock
          ScenarioBlock(
            bindings = ImmArray(block.getBindingsList.asScala).map(decodeBinding(_, definition)),
            body = decodeExpr(block.getBody, definition))

        case PLF.Scenario.SumCase.GET_TIME =>
          ScenarioGetTime

        case PLF.Scenario.SumCase.PASS =>
          ScenarioPass(decodeExpr(lfScenario.getPass, definition))

        case PLF.Scenario.SumCase.GET_PARTY =>
          ScenarioGetParty(decodeExpr(lfScenario.getGetParty, definition))

        case PLF.Scenario.SumCase.EMBED_EXPR =>
          val embedExpr = lfScenario.getEmbedExpr
          ScenarioEmbedExpr(
            decodeType(embedExpr.getType),
            decodeExpr(embedExpr.getBody, definition))

        case PLF.Scenario.SumCase.SUM_NOT_SET =>
          throw ParseError("Scenario.SUM_NOT_SET")
      }

    private[this] def decodeTypeVarWithKind(
        lfTypeVarWithKind: PLF.TypeVarWithKind): (TypeVarName, Kind) =
      handleInternedName(
        lfTypeVarWithKind.getVar,
        lfTypeVarWithKind.getVarInternedString,
        "TypeVarWithKind.var"
      ) -> decodeKind(lfTypeVarWithKind.getKind)

    private[this] def decodeBinding(lfBinding: PLF.Binding, definition: String): Binding = {
      val (binder, typ) = decodeBinder(lfBinding.getBinder)
      Binding(Some(binder), typ, decodeExpr(lfBinding.getBound, definition))
    }

    private[this] def decodeBinder(lfBinder: PLF.VarWithType): (ExprVarName, Type) =
      handleInternedName(
        lfBinder.getVar,
        lfBinder.getVarInternedString,
        "VarWithType.var"
      ) -> decodeType(lfBinder.getType)

    private[this] def decodePrimCon(lfPrimCon: PLF.PrimCon): PrimCon =
      lfPrimCon match {
        case PLF.PrimCon.CON_UNIT =>
          PCUnit
        case PLF.PrimCon.CON_FALSE =>
          PCFalse
        case PLF.PrimCon.CON_TRUE =>
          PCTrue
        case _ => throw ParseError("Unknown PrimCon: " + lfPrimCon.toString)
      }

    private[this] def decodePrimLit(lfPrimLit: PLF.PrimLit): PrimLit =
      lfPrimLit.getSumCase match {
        case PLF.PrimLit.SumCase.INT64 =>
          PLInt64(lfPrimLit.getInt64)
        case PLF.PrimLit.SumCase.DECIMAL =>
          assertUntil(LV.Features.numeric, "PrimLit.decimal")
          assertUntil(LV.Features.internedStrings, "PrimLit.decimal")
          toPLDecimal(lfPrimLit.getDecimal)
        case PLF.PrimLit.SumCase.NUMERIC =>
          assertSince(LV.Features.numeric, "PrimLit.numeric")
          assertUntil(LV.Features.internedStrings, "PrimLit.numeric")
          toPLNumeric(lfPrimLit.getNumeric)
        case PLF.PrimLit.SumCase.TEXT =>
          assertUntil(LV.Features.internedStrings, "PrimLit.text")
          PLText(lfPrimLit.getText)
        case PLF.PrimLit.SumCase.PARTY =>
          assertUntil(LV.Features.internedStrings, "PrimLit.party")
          toPLParty(lfPrimLit.getParty)
        case PLF.PrimLit.SumCase.TIMESTAMP =>
          val t = Time.Timestamp.fromLong(lfPrimLit.getTimestamp)
          t.fold(e => throw ParseError("error decoding timestamp: " + e), PLTimestamp)
        case PLF.PrimLit.SumCase.DATE =>
          val d = Time.Date.fromDaysSinceEpoch(lfPrimLit.getDate)
          d.fold(e => throw ParseError("error decoding date: " + e), PLDate)
        case PLF.PrimLit.SumCase.TEXT_INTERNED_STRING =>
          assertSince(LV.Features.internedStrings, "PrimLit.text_interned_string")
          PLText(getInternedString(lfPrimLit.getTextInternedString))
        case PLF.PrimLit.SumCase.DECIMAL_INTERNED_STRING =>
          assertUntil(LV.Features.numeric, "PrimLit.decimal_interned_string")
          assertSince(LV.Features.internedStrings, "PrimLit.decimal_interned_string")
          toPLDecimal(getInternedString(lfPrimLit.getDecimalInternedString))
        case PLF.PrimLit.SumCase.NUMERIC_INTERNED_STRING =>
          assertSince(LV.Features.numeric, "PrimLit.numeric")
          assertSince(LV.Features.internedStrings, "PrimLit.decimal_interned_string")
          toPLNumeric(getInternedString(lfPrimLit.getNumericInternedString))
        case PLF.PrimLit.SumCase.PARTY_INTERNED_STRING =>
          assertSince(LV.Features.internedStrings, "PrimLit.party_interned_string")
          toPLParty(getInternedString(lfPrimLit.getPartyInternedString))
        case PLF.PrimLit.SumCase.SUM_NOT_SET =>
          throw ParseError("PrimLit.SUM_NOT_SET")
      }
  }

  private def versionIsOlderThan(minVersion: LV): Boolean =
    LV.ordering.lt(languageVersion, minVersion)

  private def toPackageId(s: String, description: => String): PackageId = {
    assertUntil(LV.Features.internedStrings, description)
    eitherToParseError(PackageId.fromString(s))
  }

  private[this] def toName(s: String): Name =
    eitherToParseError(Name.fromString(s))

  private[this] def toPLNumeric(s: String) =
    PLNumeric(eitherToParseError(Numeric.fromString(s)))

  private[this] def toPLDecimal(s: String) =
    PLNumeric(eitherToParseError(Decimal.fromString(s)))

  private[this] def toPLParty(s: String) =
    PLParty(eitherToParseError(Party.fromString(s)))

  // maxVersion excluded
  private[this] def assertUntil(maxVersion: LV, description: => String): Unit =
    if (!versionIsOlderThan(maxVersion))
      throw ParseError(s"$description is not supported by DAML-LF 1.$minor")

  // minVersion included
  private[this] def assertSince(minVersion: LV, description: => String): Unit =
    if (versionIsOlderThan(minVersion))
      throw ParseError(s"$description is not supported by DAML-LF 1.$minor")

  private def assertNonEmpty(s: Seq[_], description: => String): Unit =
    if (s.isEmpty) throw ParseError(s"Unexpected empty $description")

  private[this] def assertEmpty(s: Seq[_], description: => String): Unit =
    if (s.nonEmpty) throw ParseError(s"Unexpected non-empty $description")

  private[this] def assertEmpty(s: util.List[_], description: => String): Unit =
    if (!s.isEmpty) throw ParseError(s"Unexpected non-empty $description")

  private[this] def assertZero(i: Int, description: => String): Unit =
    if (i != 0) throw ParseError(s"Unexpected non-zero $description")
}

private[lf] object DecodeV1 {

  @tailrec
  private def ntimes[A](n: Int, f: A => A, a: A): A =
    if (n == 0) a else ntimes(n - 1, f, f(a))

  private def eitherToParseError[A](x: Either[String, A]): A =
    x.fold(err => throw new ParseError(err), identity)

  case class BuiltinTypeInfo(
      proto: PLF.PrimType,
      bTyp: BuiltinType,
      minVersion: LV = LV.Features.default
  )

  val builtinTypeInfos: List[BuiltinTypeInfo] = {
    import PLF.PrimType._, LV.Features._
    // DECIMAL is not there and should be handled in an ad-hoc way.
    List(
      BuiltinTypeInfo(UNIT, BTUnit),
      BuiltinTypeInfo(BOOL, BTBool),
      BuiltinTypeInfo(TEXT, BTText),
      BuiltinTypeInfo(INT64, BTInt64),
      BuiltinTypeInfo(TIMESTAMP, BTTimestamp),
      BuiltinTypeInfo(PARTY, BTParty),
      BuiltinTypeInfo(LIST, BTList),
      BuiltinTypeInfo(UPDATE, BTUpdate),
      BuiltinTypeInfo(SCENARIO, BTScenario),
      BuiltinTypeInfo(CONTRACT_ID, BTContractId),
      BuiltinTypeInfo(DATE, BTDate),
      BuiltinTypeInfo(OPTIONAL, BTOptional, minVersion = optional),
      BuiltinTypeInfo(MAP, BTMap, minVersion = optional),
      BuiltinTypeInfo(ARROW, BTArrow, minVersion = arrowType),
      BuiltinTypeInfo(NUMERIC, BTNumeric, minVersion = numeric),
      BuiltinTypeInfo(ANY, BTAnyTemplate, minVersion = anyTemplate)
    )
  }

  private val builtinTypeInfoMap =
    builtinTypeInfos
      .map(info => info.proto -> info)
      .toMap

  case class BuiltinFunctionInfo(
      proto: PLF.BuiltinFunction,
      builtin: BuiltinFunction,
      minVersion: LV = LV.Features.default, // first version that does support the builtin
      maxVersion: Option[LV] = None, // first version that does not support the builtin
      implicitDecimalScaleParameters: Int = 0
  )

  val builtinFunctionInfos: List[BuiltinFunctionInfo] = {
    import PLF.BuiltinFunction._, LV.Features._
    List(
      BuiltinFunctionInfo(
        ADD_DECIMAL,
        BAddNumeric,
        maxVersion = Some(numeric),
        implicitDecimalScaleParameters = 1
      ),
      BuiltinFunctionInfo(
        SUB_DECIMAL,
        BSubNumeric,
        maxVersion = Some(numeric),
        implicitDecimalScaleParameters = 1
      ),
      BuiltinFunctionInfo(
        MUL_DECIMAL,
        BMulNumeric,
        maxVersion = Some(numeric),
        implicitDecimalScaleParameters = 3
      ),
      BuiltinFunctionInfo(
        DIV_DECIMAL,
        BDivNumeric,
        maxVersion = Some(numeric),
        implicitDecimalScaleParameters = 3
      ),
      BuiltinFunctionInfo(
        ROUND_DECIMAL,
        BRoundNumeric,
        maxVersion = Some(numeric),
        implicitDecimalScaleParameters = 1
      ),
      BuiltinFunctionInfo(ADD_NUMERIC, BAddNumeric, minVersion = numeric),
      BuiltinFunctionInfo(SUB_NUMERIC, BSubNumeric, minVersion = numeric),
      BuiltinFunctionInfo(MUL_NUMERIC, BMulNumeric, minVersion = numeric),
      BuiltinFunctionInfo(DIV_NUMERIC, BDivNumeric, minVersion = numeric),
      BuiltinFunctionInfo(ROUND_NUMERIC, BRoundNumeric, minVersion = numeric),
      BuiltinFunctionInfo(CAST_NUMERIC, BCastNumeric, minVersion = numeric),
      BuiltinFunctionInfo(SHIFT_NUMERIC, BShiftNumeric, minVersion = numeric),
      BuiltinFunctionInfo(ADD_INT64, BAddInt64),
      BuiltinFunctionInfo(SUB_INT64, BSubInt64),
      BuiltinFunctionInfo(MUL_INT64, BMulInt64),
      BuiltinFunctionInfo(DIV_INT64, BDivInt64),
      BuiltinFunctionInfo(MOD_INT64, BModInt64),
      BuiltinFunctionInfo(EXP_INT64, BExpInt64),
      BuiltinFunctionInfo(
        INT64_TO_DECIMAL,
        BInt64ToNumeric,
        maxVersion = Some(numeric),
        implicitDecimalScaleParameters = 1
      ),
      BuiltinFunctionInfo(
        DECIMAL_TO_INT64,
        BNumericToInt64,
        maxVersion = Some(numeric),
        implicitDecimalScaleParameters = 1
      ),
      BuiltinFunctionInfo(INT64_TO_NUMERIC, BInt64ToNumeric, minVersion = numeric),
      BuiltinFunctionInfo(NUMERIC_TO_INT64, BNumericToInt64, minVersion = numeric),
      BuiltinFunctionInfo(FOLDL, BFoldl),
      BuiltinFunctionInfo(FOLDR, BFoldr),
      BuiltinFunctionInfo(MAP_EMPTY, BMapEmpty, minVersion = map),
      BuiltinFunctionInfo(MAP_INSERT, BMapInsert, minVersion = map),
      BuiltinFunctionInfo(MAP_LOOKUP, BMapLookup, minVersion = map),
      BuiltinFunctionInfo(MAP_DELETE, BMapDelete, minVersion = map),
      BuiltinFunctionInfo(MAP_TO_LIST, BMapToList, minVersion = map),
      BuiltinFunctionInfo(MAP_SIZE, BMapSize, minVersion = map),
      BuiltinFunctionInfo(APPEND_TEXT, BAppendText),
      BuiltinFunctionInfo(ERROR, BError),
      BuiltinFunctionInfo(LEQ_INT64, BLessEqInt64),
      BuiltinFunctionInfo(
        LEQ_DECIMAL,
        BLessEqNumeric,
        maxVersion = Some(numeric),
        implicitDecimalScaleParameters = 1
      ),
      BuiltinFunctionInfo(LEQ_NUMERIC, BLessEqNumeric, minVersion = numeric),
      BuiltinFunctionInfo(LEQ_TEXT, BLessEqText),
      BuiltinFunctionInfo(LEQ_TIMESTAMP, BLessEqTimestamp),
      BuiltinFunctionInfo(LEQ_PARTY, BLessEqParty, minVersion = partyOrdering),
      BuiltinFunctionInfo(GEQ_INT64, BGreaterEqInt64),
      BuiltinFunctionInfo(
        GEQ_DECIMAL,
        BGreaterEqNumeric,
        maxVersion = Some(numeric),
        implicitDecimalScaleParameters = 1
      ),
      BuiltinFunctionInfo(GEQ_NUMERIC, BGreaterEqNumeric, minVersion = numeric),
      BuiltinFunctionInfo(GEQ_TEXT, BGreaterEqText),
      BuiltinFunctionInfo(GEQ_TIMESTAMP, BGreaterEqTimestamp),
      BuiltinFunctionInfo(GEQ_PARTY, BGreaterEqParty, minVersion = partyOrdering),
      BuiltinFunctionInfo(LESS_INT64, BLessInt64),
      BuiltinFunctionInfo(
        LESS_DECIMAL,
        BLessNumeric,
        maxVersion = Some(numeric),
        implicitDecimalScaleParameters = 1
      ),
      BuiltinFunctionInfo(LESS_NUMERIC, BLessNumeric, minVersion = numeric),
      BuiltinFunctionInfo(LESS_TEXT, BLessText),
      BuiltinFunctionInfo(LESS_TIMESTAMP, BLessTimestamp),
      BuiltinFunctionInfo(LESS_PARTY, BLessParty, minVersion = partyOrdering),
      BuiltinFunctionInfo(GREATER_INT64, BGreaterInt64),
      BuiltinFunctionInfo(
        GREATER_DECIMAL,
        BGreaterNumeric,
        maxVersion = Some(numeric),
        implicitDecimalScaleParameters = 1
      ),
      BuiltinFunctionInfo(GREATER_NUMERIC, BGreaterNumeric, minVersion = numeric),
      BuiltinFunctionInfo(GREATER_TEXT, BGreaterText),
      BuiltinFunctionInfo(GREATER_TIMESTAMP, BGreaterTimestamp),
      BuiltinFunctionInfo(GREATER_PARTY, BGreaterParty, minVersion = partyOrdering),
      BuiltinFunctionInfo(TO_TEXT_INT64, BToTextInt64),
      BuiltinFunctionInfo(
        TO_TEXT_DECIMAL,
        BToTextNumeric,
        maxVersion = Some(numeric),
        implicitDecimalScaleParameters = 1
      ),
      BuiltinFunctionInfo(TO_TEXT_NUMERIC, BToTextNumeric, minVersion = numeric),
      BuiltinFunctionInfo(TO_TEXT_TIMESTAMP, BToTextTimestamp),
      BuiltinFunctionInfo(TO_TEXT_PARTY, BToTextParty, minVersion = partyTextConversions),
      BuiltinFunctionInfo(TO_TEXT_TEXT, BToTextText),
      BuiltinFunctionInfo(TO_QUOTED_TEXT_PARTY, BToQuotedTextParty),
      BuiltinFunctionInfo(TEXT_FROM_CODE_POINTS, BToTextCodePoints, minVersion = textPacking),
      BuiltinFunctionInfo(FROM_TEXT_PARTY, BFromTextParty, minVersion = partyTextConversions),
      BuiltinFunctionInfo(FROM_TEXT_INT64, BFromTextInt64, minVersion = numberParsing),
      BuiltinFunctionInfo(
        FROM_TEXT_DECIMAL,
        BFromTextNumeric,
        implicitDecimalScaleParameters = 1,
        minVersion = numberParsing,
        maxVersion = Some(numeric)),
      BuiltinFunctionInfo(FROM_TEXT_NUMERIC, BFromTextNumeric, minVersion = numeric),
      BuiltinFunctionInfo(TEXT_TO_CODE_POINTS, BFromTextCodePoints, minVersion = textPacking),
      BuiltinFunctionInfo(SHA256_TEXT, BSHA256Text, minVersion = shaText),
      BuiltinFunctionInfo(DATE_TO_UNIX_DAYS, BDateToUnixDays),
      BuiltinFunctionInfo(EXPLODE_TEXT, BExplodeText),
      BuiltinFunctionInfo(IMPLODE_TEXT, BImplodeText),
      BuiltinFunctionInfo(GEQ_DATE, BGreaterEqDate),
      BuiltinFunctionInfo(LEQ_DATE, BLessEqDate),
      BuiltinFunctionInfo(LESS_DATE, BLessDate),
      BuiltinFunctionInfo(TIMESTAMP_TO_UNIX_MICROSECONDS, BTimestampToUnixMicroseconds),
      BuiltinFunctionInfo(TO_TEXT_DATE, BToTextDate),
      BuiltinFunctionInfo(UNIX_DAYS_TO_DATE, BUnixDaysToDate),
      BuiltinFunctionInfo(UNIX_MICROSECONDS_TO_TIMESTAMP, BUnixMicrosecondsToTimestamp),
      BuiltinFunctionInfo(GREATER_DATE, BGreaterDate),
      BuiltinFunctionInfo(EQUAL_INT64, BEqualInt64),
      BuiltinFunctionInfo(
        EQUAL_DECIMAL,
        BEqualNumeric,
        maxVersion = Some(numeric),
        implicitDecimalScaleParameters = 1
      ),
      BuiltinFunctionInfo(EQUAL_NUMERIC, BEqualNumeric, minVersion = numeric),
      BuiltinFunctionInfo(EQUAL_TEXT, BEqualText),
      BuiltinFunctionInfo(EQUAL_TIMESTAMP, BEqualTimestamp),
      BuiltinFunctionInfo(EQUAL_DATE, BEqualDate),
      BuiltinFunctionInfo(EQUAL_PARTY, BEqualParty),
      BuiltinFunctionInfo(EQUAL_BOOL, BEqualBool),
      BuiltinFunctionInfo(EQUAL_LIST, BEqualList),
      BuiltinFunctionInfo(EQUAL_CONTRACT_ID, BEqualContractId),
      BuiltinFunctionInfo(TRACE, BTrace),
      BuiltinFunctionInfo(COERCE_CONTRACT_ID, BCoerceContractId, minVersion = coerceContractId)
    )
  }

  private val builtinInfoMap =
    builtinFunctionInfos
      .map(info => info.proto -> info)
      .toMap
      .withDefault(_ => throw ParseError("BuiltinFunction.UNRECOGNIZED"))

}
