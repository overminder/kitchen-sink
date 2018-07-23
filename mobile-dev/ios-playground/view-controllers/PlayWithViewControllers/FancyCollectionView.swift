//
// Created by Yuxiang JIANG on 7/22/18.
// Copyright (c) 2018 Yuxiang JIANG. All rights reserved.
//

import UIKit

private let reuseId = "TableLikeCell"
private let headerReuseId = "TableLikeCell"

private func mkFlowLayout() -> UICollectionViewFlowLayout {
    let layout = UICollectionViewFlowLayout()
    return layout
}

class TableLikeCollectionViewHeader: UICollectionReusableView {
    override func prepareForReuse() {
        super.prepareForReuse()

        miscExtRemoveAllSubviews()
    }

    func bindSectionModel(_ m: LabelSectionModel) {
        let v = UILabel()
        v.backgroundColor = .white
        v.text = m.sectionHeader
        addSubview(v)
        ConstraintSet.fit(v, into: self)
    }
}

class TableLikeCollectionView: UICollectionViewController, UICollectionViewDelegateFlowLayout {
    var data: LabelCollectionModel = .sample
    var mutator = LabelCollectionModelMutator()
    let refreshControl = UIRefreshControl()

    init() {
        super.init(collectionViewLayout: mkFlowLayout())

        self.collectionView?.backgroundColor = .lightGray
    }

    required init(coder: NSCoder) {
        fatalError()
    }

    override func viewDidLoad() {
        super.viewDidLoad()

        collectionView?.register(UICollectionViewCell.self, forCellWithReuseIdentifier: reuseId)
        collectionView?.register(TableLikeCollectionViewHeader.self,
                forSupplementaryViewOfKind: UICollectionElementKindSectionHeader,
                withReuseIdentifier: headerReuseId)
        collectionView?.refreshControl = refreshControl
        refreshControl.addTarget(self, action: #selector(refresh), for: .valueChanged)
    }

    @objc
    private func refresh() {
        DispatchQueue.main.asyncAfter(deadline: .now() + 0.5) { [weak self] in
            self?.doRefresh()
        }
    }

    func doRefresh() {
        if refreshControl.isRefreshing {
            mutator.mutate(&data)
            collectionView?.reloadSections(IndexSet(integer: 0))
            refreshControl.endRefreshing()
        }
    }

    override func numberOfSections(in collectionView: UICollectionView) -> Int {
        return data.sections.count
    }

    override func collectionView(_ collectionView: UICollectionView, numberOfItemsInSection section: Int) -> Int {
        return self.section(forIx: section)?.viewModels.count ?? 0
    }

    override func collectionView(_ collectionView: UICollectionView, cellForItemAt indexPath: IndexPath) -> UICollectionViewCell {
        let cell = collectionView.dequeueReusableCell(withReuseIdentifier: reuseId, for: indexPath)
        cell.miscExtRemoveAllSubviews()
        if let item = item(forSection: indexPath.section, item: indexPath.item) {
            item.bindCollectionView(cell)
        }
        return cell
    }

    func collectionView(_ collectionView: UICollectionView, layout collectionViewLayout: UICollectionViewLayout, sizeForItemAt indexPath: IndexPath) -> CGSize {
        let w = (collectionView.bounds.width - 10) / 2
        return CGSize(width: w, height: 60)
    }

    // func collectionView(_ collectionView: UICollectionView, layout collectionViewLayout: UICollectionViewLayout, insetForSectionAt section: Int) -> UIEdgeInsets {
    //     return UIEdgeInsets(top: 20, left: 10, bottom: 10, right: 10)
    // }

    func collectionView(_ collectionView: UICollectionView, layout collectionViewLayout: UICollectionViewLayout, referenceSizeForHeaderInSection section: Int) -> CGSize {
        return CGSize(width: 220, height: 60)
    }

    override func collectionView(_ collectionView: UICollectionView, viewForSupplementaryElementOfKind kind: String, at indexPath: IndexPath) -> UICollectionReusableView {
        if kind == UICollectionElementKindSectionHeader {
            let v = collectionView.dequeueReusableSupplementaryView(ofKind: kind,
                    withReuseIdentifier: headerReuseId, for: indexPath)
            if let v = v as? TableLikeCollectionViewHeader {
                if let section = section(forIx: indexPath.section) {
                    v.bindSectionModel(section)
                }
            }
            return v
        } else {
            return super.collectionView(collectionView, viewForSupplementaryElementOfKind: kind, at: indexPath)
        }
    }

    override func collectionView(_ collectionView: UICollectionView, didSelectItemAt indexPath: IndexPath) {
        super.collectionView(collectionView, didSelectItemAt: indexPath)
    }
}

extension TableLikeCollectionView {
    private func section(forIx ix: Int) -> LabelSectionModel? {
        return data.sections[safe: ix]
    }

    private func item(forSection sectionIx: Int, item: Int) -> LabelViewModel? {
        return section(forIx: sectionIx)?.viewModels[safe: item]
    }
}

