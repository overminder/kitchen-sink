# Use a prebuilt llvm toolchain at $LLVM_ROOT for faster compilation.
# Point $NDK_STANDALONE to your Android NDK's standalone toolchains.
# Enable ccache for a faster rebuild.

./configure \
    --target=i686-linux-android,arm-linux-androideabi \
    --llvm-root=$LLVM_ROOT \
    --enable-ccache \
    --i686-linux-android-ndk=$NDK_STANDALONE \
    --arm-linux-androideabi-ndk=$NDK_STANDALONE
