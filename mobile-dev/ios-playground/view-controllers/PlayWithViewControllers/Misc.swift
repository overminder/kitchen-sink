//
// Created by Yuxiang JIANG on 7/21/18.
// Copyright (c) 2018 Yuxiang JIANG. All rights reserved.
//

import UIKit

extension Collection {
    public subscript(safe ix: Index) -> Element? {
        if ix >= startIndex && ix < endIndex {
            return self[ix]
        } else {
            return nil
        }
    }
}

typealias Thunk<A> = () -> A

typealias DisplayableAction = (
    text: String,
    mkAction: Thunk<Action>?
)

func mkConstraintView() -> UIView {
    let v = UIView()
    // Avoid having too many constraints
    v.translatesAutoresizingMaskIntoConstraints = false
    return v
}

let fancyBlue = UIColor(red:0.05, green:0.47, blue:1.00, alpha:1.0)

struct LabelCollectionModel {
    var sections: [LabelSectionModel]

    static let sample = LabelCollectionModel(sections: [
        LabelSectionModel(sectionHeader: "Intro.", viewModels: [
            LabelViewModel(caption: "What is Foo"),
            LabelViewModel(caption: "Why are we motivated"),
        ]),
        LabelSectionModel(sectionHeader: "Background.", viewModels: [
            LabelViewModel(caption: "What is Foo.Bar"),
            LabelViewModel(caption: "What is Foo.Baz"),
        ]),
        LabelSectionModel(sectionHeader: "Methodology.", viewModels: [
            LabelViewModel(caption: "How to implement Foo"),
            LabelViewModel(caption: "How to implement Foo.Bar"),
            LabelViewModel(caption: "How to implement Foo.Baz"),
        ]),
        LabelSectionModel(sectionHeader: "Evaluation.", viewModels: [
            LabelViewModel(caption: "How fast is Foo"),
        ]),
        LabelSectionModel(sectionHeader: "Conclusion.", viewModels: [
            LabelViewModel(caption: "How good is our method"),
            LabelViewModel(caption: "How good is the other method"),
        ]),
    ])
}

struct LabelSectionModel {
    var sectionHeader: String
    var viewModels: [LabelViewModel]
}

struct LabelViewModel {
    var caption: String

    func bindTableView(_ c: UITableViewCell) {
        c.textLabel?.text = caption
        c.backgroundColor = UIColor.white
    }

    func bindCollectionView(_ c: UICollectionViewCell) {
        let label = UILabel()
        label.text = caption
        c.backgroundColor = UIColor.white
        c.addSubview(label)
        ConstraintSet.fit(label, into: c)
    }
}

struct ConstraintSet {
    static func fit(_ view: UIView, into: UIView) {
        view.translatesAutoresizingMaskIntoConstraints = false
        let guide = into.layoutMarginsGuide

        view.topAnchor.constraint(equalTo: guide.topAnchor).isActive = true
        view.leadingAnchor.constraint(equalTo: guide.leadingAnchor).isActive = true
        view.trailingAnchor.constraint(equalTo: guide.trailingAnchor).isActive = true
        view.bottomAnchor.constraint(equalTo: guide.bottomAnchor).isActive = true
    }
}

extension UIView {
    func miscExtRemoveAllSubviews() {
        for v in subviews {
            v.removeFromSuperview()
        }
    }
}
