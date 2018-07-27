//
// Created by Yuxiang JIANG on 7/26/18.
// Copyright (c) 2018 Yuxiang JIANG. All rights reserved.
//

import UIKit

class NestedParentVC: UIViewController {
    let ixChooser = UISegmentedControl()
    let childrenContainerView = UIView()
    let addVCButton = UIButton(type: .roundedRect)
    var allChildrenV = [UIView]()
    var currentChildV: UIView?

    init() {
        super.init(nibName: nil, bundle: nil)
    }

    required init(coder: NSCoder) {
        fatalError()
    }

    override func viewDidLoad() {
        super.viewDidLoad()

        view.backgroundColor = .white

        ixChooser.translatesAutoresizingMaskIntoConstraints = false
        ixChooser.addTarget(self, action: #selector(chooserChanged), for: .valueChanged)
        view.addSubview(ixChooser)

        childrenContainerView.translatesAutoresizingMaskIntoConstraints = false
        childrenContainerView.backgroundColor = .blue
        view.addSubview(childrenContainerView)

        addVCButton.translatesAutoresizingMaskIntoConstraints = false
        addVCButton.setTitle("Add" , for: .normal)
        addVCButton.addTarget(self, action: #selector(addClicked), for: .touchDown)
        view.addSubview(addVCButton)

        let guide = view.layoutMarginsGuide

        ixChooser.heightAnchor.constraint(equalToConstant: 80).isActive = true
        addVCButton.heightAnchor.constraint(equalToConstant: 80).isActive = true
        addVCButton.widthAnchor.constraint(equalToConstant: 80).isActive = true
        ixChooser.topAnchor.constraint(equalTo: guide.topAnchor).isActive = true
        addVCButton.topAnchor.constraint(equalTo: guide.topAnchor).isActive = true
        ixChooser.bottomAnchor.constraint(equalTo: childrenContainerView.topAnchor).isActive = true
        ixChooser.leadingAnchor.constraint(equalTo: guide.leadingAnchor).isActive = true
        ixChooser.trailingAnchor.constraint(equalTo: addVCButton.leadingAnchor).isActive = true
        addVCButton.trailingAnchor.constraint(equalTo: guide.trailingAnchor).isActive = true

        childrenContainerView.leadingAnchor.constraint(equalTo: guide.leadingAnchor).isActive = true
        childrenContainerView.trailingAnchor.constraint(equalTo: guide.trailingAnchor).isActive = true
        childrenContainerView.bottomAnchor.constraint(equalTo: guide.bottomAnchor).isActive = true
    }

    @objc
    private func addClicked() {
        let nth = childViewControllers.count
        let color = colors[nth % colors.count]
        let c = ColoredChildVC(color: color, nth: nth)
        // let c = MutableTableViewController(color: color)
        // allChildrenVC.append(c)
        addChildViewController(c)
        c.didMove(toParentViewController: self)
        presentView(ofController: c)
        ixChooser.insertSegment(withTitle: "\(nth)", at: nth, animated: true)

        print("Add clicked: \(nth)")
    }

    private func presentView(ofController vc: UIViewController) {
        let wrapperView = mkConstraintView()
        childrenContainerView.addSubview(wrapperView)
        wrapperView.addSubview(vc.view)
        ConstraintSet.fit(vc.view, into: wrapperView)
        ConstraintSet.fit(wrapperView, into: childrenContainerView)
        wrapperView.isHidden = true
        allChildrenV.append(wrapperView)
    }

    @objc
    private func chooserChanged() {
        let ix = ixChooser.selectedSegmentIndex
        print("willSwitchTo \(ix)")

        // if let c = allChildrenVC[safe: ix] {
        if let c = allChildrenV[safe: ix] {
            if let curr = currentChildV {
                // curr.removeFromParentViewController()
                curr.isHidden = true
            }
            // addChildViewController(c)
            // childrenContainerView.miscExtRemoveAllSubviews()
            // childrenContainerView.miscExtRemoveAllConstraints()
            // childrenContainerView.addSubview(c.view)
            // ConstraintSet.fit(c.view, into: childrenContainerView)
            c.isHidden = false
            currentChildV = c
        }
    }
}

private let colors: [UIColor] = [
    .lightGray,
    .black,
    .yellow,
    .blue,
    .brown,
    .cyan,
    .magenta,
    .orange,
]

class ColoredChildVC: UIViewController {
    let color: UIColor
    let nth: Int

    init(color: UIColor, nth: Int) {
        self.color = color
        self.nth = nth
        super.init(nibName: nil, bundle: nil)
        log()
    }

    required init(coder: NSCoder) {
        fatalError()
    }

    deinit {
        print("ColoredChildVC deinit")
    }

    func log(_ funcName: String = #function) {
        print("ColorChildVC(\(nth)).\(funcName)()")
    }

    override func loadView() {
        super.loadView()

        log()
    }

    override func viewDidLoad() {
        super.viewDidLoad()

        log()

        view.backgroundColor = color
    }

    override func viewWillAppear(_ animated: Bool) {
        super.viewWillAppear(animated)
        log()
    }

    override func viewDidAppear(_ animated: Bool) {
        super.viewDidAppear(animated)
        log()
    }

    override func viewWillDisappear(_ animated: Bool) {
        super.viewWillDisappear(animated)
        log()
    }

    override func viewDidDisappear(_ animated: Bool) {
        super.viewDidDisappear(animated)
        log()
    }
}
