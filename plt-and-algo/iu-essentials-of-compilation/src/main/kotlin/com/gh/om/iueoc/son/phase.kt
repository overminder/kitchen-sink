package com.gh.om.iueoc.son

interface Phase {
    // Returns true if [g] was changed.
    fun run(g: MutGraph): Boolean
}