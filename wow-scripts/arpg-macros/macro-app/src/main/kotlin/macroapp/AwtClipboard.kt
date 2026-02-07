package macroapp

import macrocore.Clipboard
import java.awt.Toolkit
import java.awt.datatransfer.DataFlavor
import java.awt.datatransfer.StringSelection

class AwtClipboard : Clipboard {
    private val clipboard = Toolkit.getDefaultToolkit().systemClipboard

    override fun getText(): String? {
        return try {
            if (clipboard.isDataFlavorAvailable(DataFlavor.stringFlavor)) {
                clipboard.getData(DataFlavor.stringFlavor) as? String
            } else {
                null
            }
        } catch (_: Exception) {
            null
        }
    }

    override fun setText(text: String) {
        clipboard.setContents(StringSelection(text), null)
    }
}
