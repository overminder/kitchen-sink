package com.github.om.inctc.lang.stlc

sealed class Type
object TyInt: Type()
object TyBool: Type()
// Not yet specialized.
data class TyVar(val id: Int): Type()
data class TyArr(val from: Type, val to: Type): Type()
