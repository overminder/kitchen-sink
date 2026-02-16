# Idea: Showing more information in the overlay during crafting

This doc discusses the feature idea of making the overlay "persistent" during macro execution,
to show rich information during the macro running process (e.g. number of currencies used
during the crafting, time elapsed) and after it ends.

The macro running state tracking is purely data-driven and can be discussed later. The below sections discuss the platform dependent aspects from this idea:
- The overlay needs to not intercept mouse clicks (because it's shown while the macro runs, which may click through it)
- The screen capture routine needs to not capture the overlay (because macros may need to capture the screen to decide what to do)

## Creating a click-through overlay

This section outlines the steps to modify the Jetpack Compose overlay to be "click-through", meaning it won't intercept mouse clicks, and they will pass to the window underneath (the game).

The solution involves using the Java Native Access (JNA) library to modify the underlying window's properties.

1.  **Add JNA Dependencies:**
    The JNA library is required to interact with native Windows APIs from Kotlin/Java. I will add the necessary dependencies (`jna` and `jna-platform`) to the `build.gradle.kts` file of the `macro-overlay` module.

2.  **Create a Click-Through Utility:**
    I will write a Kotlin object, say `WindowUtils`, with a function that takes a window handle and sets the `WS_EX_TRANSPARENT` extended window style. This style tells Windows that the window should be transparent to mouse events. This will be implemented using JNA.

3.  **Integrate with Jetpack Compose `Window`:**
    I will show how to modify your existing `Window` composable. The key is to get access to the underlying `JFrame` and its native window handle. This handle is then passed to the utility function created in the previous step. This is typically done inside a `LaunchedEffect` or `DisposableEffect` to apply the style when the window is created.

## Capturing Game Content without the Overlay

Using `java.awt.Robot` will capture the overlay along with the game. To capture only the game's content, the recommended approach is the **Windows Graphics Capture API**. This is a non-trivial task that involves interoperating with modern Windows APIs from the JVM.

### High-Level Steps for Implementation

1.  **Find a WinRT Interop Library:**
    The Windows Graphics Capture API is a WinRT (Windows Runtime) API, which isn't directly callable from Java/Kotlin. A third-party library is needed to bridge the JVM and WinRT. You would need to research and choose a suitable library by searching for "Java WinRT interop" or similar terms. This is the most critical and potentially complex prerequisite.

2.  **Get the Game's Window Handle (`HWND`):**
    The capture API needs a handle to the target window. This can be obtained using the `FindWindow` function from the User32 library (via JNA, which you will already have as a dependency). You would typically find the window by its title.

3.  **Implement the Capture Flow:**
    Once you have a WinRT interop library, the general flow is:
    a.  Initialize the Windows Runtime environment for the current thread.
    b.  Get a `GraphicsCaptureItem` for the game's window handle.
    c.  Create a `Direct3D11Device` which is needed for the capture session.
    d.  Create a `GraphicsCaptureSession` from the `GraphicsCaptureItem`.
    e.  Create a frame pool to receive captured frames from the session.
    f.  Register a callback to be notified when new frames are available in the pool.

4.  **Process Captured Frames (GPU -> CPU):**
    The frames arrive as DirectX 11 textures, which exist on the GPU. To be useful as an image in your application (e.g., a `BufferedImage`), they must be copied to the CPU's main memory.
    a.  This involves creating a temporary "staging" texture that is CPU-readable.
    b.  Copying the captured frame from the GPU texture to the staging texture.
    c.  "Mapping" the staging texture to get access to the raw pixel data in system memory.
    d.  Creating a `BufferedImage` from the raw pixel data, being careful to handle the correct pixel format (e.g., BGRA vs. ARGB).

This approach is powerful and correct, but as you can see, it's significantly more involved than using `java.awt.Robot`.
