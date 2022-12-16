### Use case

+ A root SwipeRefreshLayout
  * A CoordinatorLayout
    - A collapsable header (e.g. via AppBarLayout.Behavior)
    - A sticky tab header (e.g. a TabLayout)
    - A tab body containing a bunch of pages (e.g. a ViewPager2 + ABL.ScrollingViewBehavior)
      * Each page contains a list of items, potentially infinitely scrolling
        (e.g. a RecyclerView)
      * Supports horizontal swipe gesture to switch between tabs

### Issues

A parent SwipeRefreshLayout competes with child ViewPager2 on touch
events.

### Ideas

The idea is to disable SRL / use SRL.OnChildScrollUpCallback to
prevent SRL from taking touch events.

One difference is that SRL.OnChildScrollUpCallback is not preemptive:
Once SRL starts intercepting touch events, there's no way to stop the
interception by returning true in OnChildScrollUpCallback. OTOH,
SRL.setEnabled(false) is preemptive.

### A (hacky) solution

Do all of below:

1. Disable SRL when VP2 is being dragged (state != IDLE)
   + This is self explanatory: when VP2 is being dragged, the gesture
     should be interpreted as a horizontal swipe, so SRL shouldn't
     even see this gesture at all.

     We have to use preemptive disable, because SRL (as a parent view)
     receives the gesture before VP2 realizes that it's a swipe (VP2
     has a touch slop).

2. Return true from SRL.OnChildScrollUpCallback, when the collapsable
   header's offsetTop != 0 (i.e. can be further moved down by scrolling up).

   + This doesn't need to be preemptive, because ABL.Behavior doesn't
     have a touch slop?

3. When a page in VP2 enters the screen while the collapsable header
   is not yet fully collapsed, reset that page's RV's vertical scroll
   offset to 0.

   + This prevents the edge case of switching between two pages with
     different RV vertical offset, which breaks the invariant
     that ABL must be fully hidden before VP2 can be scrolled (which
     SRL relies on in the check in OnChildScrollUpCallback).

### Can we do better?

I'm sure we can! There's no reason that touch handling is such an
ambiguous mess.

