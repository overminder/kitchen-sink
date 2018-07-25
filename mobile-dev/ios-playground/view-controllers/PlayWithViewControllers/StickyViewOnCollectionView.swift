//
// Created by Yuxiang JIANG on 7/24/18.
// Copyright (c) 2018 Yuxiang JIANG. All rights reserved.
//

import UIKit

private let navAndStatusBarHeight = 44 /* Nav */ + 20 /* Status */

class StickyVC: UIViewController {
    let collView = UICollectionView(frame: .zero, collectionViewLayout: UICollectionViewFlowLayout.init())
    let boxView = UIView()
    let boxView2 = UIView()
    let boxView3 = UIView()

    override func viewDidLoad() {
        view.addSubview(collView)
        ConstraintSet.fit(collView, into: view)

        boxView.backgroundColor = .green
        boxView2.backgroundColor = .red
        boxView3.backgroundColor = .blue
        setBoxFrames(yOffset: 0)
        // Note the zindex.
        view.addSubview(boxView2)
        view.addSubview(boxView)
        view.addSubview(boxView3)

        collView.backgroundColor = .lightGray
        collView.register(UICollectionViewCell.self, forCellWithReuseIdentifier: reuseId)
        collView.delegate = self
        collView.dataSource = self
    }

    private func setBoxFrames(yOffset: Int) {
        let baseY = navAndStatusBarHeight + 50 + yOffset
        func sticky(_ y: Int, to: Int = 0) -> Int {
            return max(navAndStatusBarHeight + to, y)
        }
        boxView.frame = CGRect(x: 0, y: sticky(baseY), width: 100, height: 50)
        // XXX: Need to clip boxView2 or it can be seen through the glossy nav bar...
        boxView2.frame = CGRect(x: 0, y: baseY + 50, width: 100, height: 50)
        boxView3.frame = CGRect(x: 0, y: sticky(baseY + 100, to: 50), width: 100, height: 50)
    }
}

private let reuseId = "StickyVCCell"

extension StickyVC: UICollectionViewDataSource, UICollectionViewDelegateFlowLayout {
    func numberOfSections(in collectionView: UICollectionView) -> Int {
        return 1
    }

    public func collectionView(_ collectionView: UICollectionView, numberOfItemsInSection section: Int) -> Int {
        return 100
    }

    func collectionView(_ collectionView: UICollectionView, cellForItemAt indexPath: IndexPath) -> UICollectionViewCell {
        let cell = collectionView.dequeueReusableCell(withReuseIdentifier: reuseId, for: indexPath)
        cell.miscExtRemoveAllSubviews()
        cell.backgroundColor = .white
        let label = UILabel()
        label.text = "Item-\(indexPath.item)"
        cell.addSubview(label)
        ConstraintSet.fit(label, into: cell)
        return cell
    }

    func collectionView(_ collectionView: UICollectionView, layout collectionViewLayout: UICollectionViewLayout, insetForSectionAt section: Int) -> UIEdgeInsets {
        return UIEdgeInsets(top: 15, left: 0, bottom: 0, right: 0)
    }

    func collectionView(_ collectionView: UICollectionView, layout collectionViewLayout: UICollectionViewLayout, sizeForItemAt indexPath: IndexPath) -> CGSize {
        return CGSize(width: collectionView.bounds.width, height: 60)
    }

    func scrollViewDidScroll(_ scrollView: UIScrollView) {
        setBoxFrames(yOffset: Int(-scrollView.contentOffset.y))
    }
}
