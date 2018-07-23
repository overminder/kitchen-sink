//
// Created by Yuxiang JIANG on 7/21/18.
// Copyright (c) 2018 Yuxiang JIANG. All rights reserved.
//

import UIKit

enum Route {
    case rootMenu
    case playground
    case alert(title: String, message: String)
    case manualLayout
    case autoLayout
    case semiAutoLayout
    case fancyTable
    case autoLayoutManyBoxes
    case mutableTableView
    case tabLikeCollView
}

enum Action {
    case pop
    case push(Route)
    case presentHere(Route)
}


let menuActions: [DisplayableAction] = [
    ("Alert(Hello)", {
        Action.presentHere(.alert(title: "Hello", message: "World"))
    }),
    ("RootMenu", {
        Action.push(.rootMenu)
    }),
    ("ManualLayout", {
        Action.push(.manualLayout)
    }),
    ("AutoLayout", {
        Action.push(.autoLayout)
    }),
    ("SemiAutoLayout", {
        Action.push(.semiAutoLayout)
    }),
    ("FancyTable", {
        Action.push(.fancyTable)
    }),
    ("AutoLayoutManyBoxes", {
        Action.push(.autoLayoutManyBoxes)
    }),
    ("MutableTableView", {
        Action.push(.mutableTableView)
    }),
    ("TableLikeCollectionView", {
        Action.push(.tabLikeCollView)
    }),
    ("Playground", {
        Action.push(.playground)
    }),
    ("Pop", {
        Action.pop
    }),
]

protocol DispatcherDelegate {
    var navigationController: UINavigationController? { get }
    var viewController: UIViewController? { get }
}

struct Dispatcher {
    func dispatch(_ action: Action?, delegate: DispatcherDelegate) {
        guard let action = action else {
            return
        }

        switch action {
        case .pop:
            delegate.navigationController?.popViewController(animated: true)
        case .push(let route):
            delegate.navigationController?.pushViewController(viewController(fromRoute: route), animated: true)
        case .presentHere(let route):
            delegate.viewController?.present(viewController(fromRoute: route), animated: true)
        }
    }

    private func viewController(fromRoute route: Route) -> UIViewController {
        switch route {
        case .rootMenu:
            return RootMenuViewController()
        case .playground:
            return PlaygroundVC()
        case .alert(let title, let message):
            let alert = UIAlertController(title: title, message: message, preferredStyle: .alert)
            alert.addAction(UIAlertAction(title: "Dismiss", style: .cancel))
            return alert
        case .manualLayout:
            return ConstraintLayoutBag().manualLayoutVC()
        case .autoLayout:
            return ConstraintLayoutBag().autoLayoutVC()
        case .semiAutoLayout:
            return ConstraintLayoutBag().semiAutoLayoutVC()
        case .autoLayoutManyBoxes:
            return MoarConstraintLayouts().makeVC()
        case .fancyTable:
            return FancyTableViewController()
        case .mutableTableView:
            return MutableTableViewController()
        case .tabLikeCollView:
            return TableLikeCollectionView()
        }
    }
}

let globalDispatcher = Dispatcher()
