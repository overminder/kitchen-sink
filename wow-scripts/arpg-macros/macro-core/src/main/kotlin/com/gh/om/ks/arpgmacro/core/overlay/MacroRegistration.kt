package com.gh.om.ks.arpgmacro.core.overlay

/**
 * Describes a macro for the overlay GUI.
 * The GUI renders these as a list of selectable items, grouped by category.
 */
data class MacroRegistration(
    val id: String,
    val name: String,
    val category: String,
    val description: String = "",
    /** Which game(s) this macro applies to, or empty for "any game". */
    val gameFilter: Set<String> = emptySet(),
)
