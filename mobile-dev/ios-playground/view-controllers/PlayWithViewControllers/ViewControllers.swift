//
//  ViewController.swift
//  PlayWithViewControllers
//
//  Created by Yuxiang JIANG on 7/9/18.
//  Copyright © 2018 Yuxiang JIANG. All rights reserved.
//

import UIKit

// MARK: ViewBag

class ViewBag {
    private var views = [UIView]()
    weak var delegate: ViewBagDelegate?
    var alertButton: UIButton?
    var vcButton: UIButton?
    var popButton: UIButton?
    var nextButtonIx = 0

    init(delegate: ViewBagDelegate? = nil) {
        self.delegate = delegate
    }
    
    func remember<A: UIView>(_ v: A) -> A {
        views.append(v)
        return v
    }
    
    func populateViews() {
        alertButton = createButtonView(text: "Alert")
        vcButton = createButtonView(text: "VC")
        popButton = createButtonView(text: "Pop")
        _ = createAnimatedBoxView()
        withVc {
            for v in views {
                $0.view.addSubview(v)
            }
        }
    }
    
    func createButtonView(text: String) -> UIButton {
        let b = UIButton(type: .roundedRect)
        b.backgroundColor = UIColor.lightGray
        b.frame = CGRect(x: 0, y: 50 * nextButtonIx, width: 100, height: 40)
        nextButtonIx += 1
        b.setTitle(text, for: .normal)
        b.addTarget(self, action: #selector(buttonClicked), for: .touchDown)
        return remember(b)
    }

    func createAnimatedBoxView() -> UIView {
        let v = UIView()
        v.backgroundColor = UIColor.gray
        v.frame = CGRect(x: 50, y: 50, width: 50, height: 50)
        
        func attachAnimation(_ v: UIView) {
            UIView.animate(withDuration: 5) {
                v.frame.origin.x += 50
                v.frame.origin.y += 50
                v.backgroundColor = UIColor.red
            }
        }
        
        attachAnimation(v)
        return remember(v)
    }

    @objc
    func buttonClicked(_ sender: UIButton, forEvent event: UIEvent) {
        if sender == alertButton {
            let alert = UIAlertController(title: "Title", message: "Message", preferredStyle: .alert)
            alert.addAction(UIAlertAction(title: "Dismiss", style: .cancel))
            withVc {
                $0.present(alert, animated: true)
            }
        } else if sender == vcButton {
            withVc {
                $0.present(PlaygroundVC(), animated: true)
            }
        } else if sender == popButton {
            withVc {
                $0.dismiss(animated: true)
            }
        }
    }
    
    func withVc(_ block: (UIViewController) -> Void) {
        if let vc = delegate?.asViewController() {
            block(vc)
        }
    }
}

// MARK: PlaygroundVC

protocol ViewBagDelegate: class {
    func asViewController() -> UIViewController?
}

class PlaygroundVC: UIViewController {
    let bag = ViewBag()
    
    override func viewDidLoad() {
        super.viewDidLoad()

        view.backgroundColor = UIColor.white
        bag.delegate = self
        bag.populateViews()
    }
}

extension PlaygroundVC: ViewBagDelegate {
    func asViewController() -> UIViewController? {
        return self
    }
}

// MARK: TableVC
