//
// Created by Yuxiang JIANG on 7/20/18.
// Copyright (c) 2018 Yuxiang JIANG. All rights reserved.
//

import UIKit

struct ConstraintLayoutBag {
    let blue = mkConstraintView()
    let red = mkConstraintView()

    init() {
        blue.backgroundColor = fancyBlue
        red.backgroundColor = UIColor.red
    }

    func applyManualLayout(_ v: UIView) {
        blue.frame = CGRect(x: 0, y: 100, width: 50, height: 100)
        red.frame = CGRect(x: 60, y: 100, width: 50, height: 100)
    }

    func applyAutoLayout(_ v: UIView) {
        let margins = v.layoutMarginsGuide
        blue.topAnchor.constraint(equalTo: margins.topAnchor).isActive = true
        blue.leadingAnchor.constraint(equalTo: margins.leadingAnchor).isActive = true
        blue.trailingAnchor.constraint(equalTo: margins.trailingAnchor).isActive = true
        blue.heightAnchor.constraint(equalTo: margins.heightAnchor, multiplier: 0.5).isActive = true

        red.bottomAnchor.constraint(equalTo: margins.bottomAnchor).isActive = true
        red.leadingAnchor.constraint(equalTo: margins.leadingAnchor).isActive = true
        red.trailingAnchor.constraint(equalTo: margins.trailingAnchor).isActive = true
        red.heightAnchor.constraint(equalTo: margins.heightAnchor, multiplier: 0.5).isActive = true
    }

    func applySemiAutoLayout(_ v: UIView) {
        let margins = v.layoutMarginsGuide
        blue.topAnchor.constraint(equalTo: margins.topAnchor).isActive = true
        blue.heightAnchor.constraint(equalToConstant: 100).isActive = true
        // Either way it's doable. blue.bot = red.top - 10 or red.top = blue.bot + 10
        blue.bottomAnchor.constraint(equalTo: red.topAnchor, constant: -10).isActive = true
        blue.leadingAnchor.constraint(equalTo: margins.leadingAnchor).isActive = true
        blue.trailingAnchor.constraint(equalTo: margins.trailingAnchor).isActive = true

        red.bottomAnchor.constraint(equalTo: margins.bottomAnchor).isActive = true
        red.leadingAnchor.constraint(equalTo: margins.leadingAnchor).isActive = true
        red.trailingAnchor.constraint(equalTo: margins.trailingAnchor).isActive = true
    }

    private func makeVC(_ block: (UIView) -> Void) -> UIViewController {
        let vc = UIViewController()
        bindToParent(view: vc.view)
        block(vc.view)
        vc.view.backgroundColor = UIColor.white
        return vc
    }

    func manualLayoutVC() -> UIViewController {
        return makeVC(applyManualLayout)
    }

    func autoLayoutVC() -> UIViewController {
        return makeVC(applyAutoLayout)
    }

    func semiAutoLayoutVC() -> UIViewController {
        return makeVC(applySemiAutoLayout)
    }

    func bindToParent(view: UIView) {
        view.addSubview(blue)
        view.addSubview(red)
    }
}

struct MoarConstraintLayouts {
    func makeVC() -> UIViewController {
        let count = 47

        let vc = UIViewController()
        vc.view.backgroundColor = UIColor.white

        let guide = vc.view.layoutMarginsGuide

        let views: [UIView] = (0..<count).map { (i: Int) -> UIView in
            let v = mkConstraintView()
            if i % 2 == 0 {
                v.backgroundColor = UIColor.red
            } else {
                v.backgroundColor = UIColor.blue
            }
            vc.view.addSubview(v)
            v.leadingAnchor.constraint(equalTo: guide.leadingAnchor).isActive = true
            v.trailingAnchor.constraint(equalTo: guide.trailingAnchor).isActive = true
            return v
        }


        var lastView: UIView?
        for (ix, v) in views.enumerated() {
            if ix == 0 {
                v.topAnchor.constraint(equalTo: guide.topAnchor).isActive = true
            }
            if let lv = lastView {
                lv.heightAnchor.constraint(equalTo: v.heightAnchor, multiplier: 1.3).isActive = true
                lv.bottomAnchor.constraint(equalTo: v.topAnchor).isActive = true
            }
            lastView = v
        }
        lastView?.bottomAnchor.constraint(equalTo: guide.bottomAnchor).isActive = true
        return vc
    }
}

