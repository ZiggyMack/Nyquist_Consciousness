
import React, { useState } from 'react';
import { symbols, axioms, domains } from '../data/pxl';

const TabButton: React.FC<{ active: boolean, onClick: () => void, children: React.ReactNode }> = ({ active, onClick, children }) => (
    <button
        onClick={onClick}
        className={`px-4 py-2 text-sm font-semibold rounded-t-lg transition-colors focus:outline-none ${active ? 'bg-slate-700/50 text-cyan-400 border-b-2 border-cyan-400' : 'bg-transparent text-slate-400 hover:bg-slate-800/50'}`}
    >
        {children}
    </button>
);

const Explanation: React.FC = () => {
    const [activeTab, setActiveTab] = useState('axioms');

    return (
        <div className="bg-slate-800/30 p-6 rounded-xl border border-slate-700/50 shadow-lg">
            <h2 className="text-xl font-bold text-white mb-4">PXL Formal System</h2>

            <div className="border-b border-slate-700">
                <nav className="-mb-px flex space-x-2" aria-label="Tabs">
                    <TabButton active={activeTab === 'axioms'} onClick={() => setActiveTab('axioms')}>Axioms</TabButton>
                    <TabButton active={activeTab === 'symbols'} onClick={() => setActiveTab('symbols')}>Symbol Key</TabButton>
                    <TabButton active={activeTab === 'domains'} onClick={() => setActiveTab('domains')}>Domains</TabButton>
                </nav>
            </div>

            <div className="py-4">
                {activeTab === 'axioms' && (
                    <div className="space-y-3">
                        {axioms.map(axiom => (
                            <div key={axiom.id} className="p-3 bg-slate-800/50 rounded-md">
                                <p className="font-mono text-cyan-400">{axiom.id}: {axiom.text}</p>
                                <p className="text-sm text-slate-400 mt-1">{axiom.description}</p>
                            </div>
                        ))}
                    </div>
                )}
                {activeTab === 'symbols' && (
                    <div className="space-y-3">
                        {symbols.map(s => (
                            <div key={s.symbol} className="flex items-start space-x-4 p-3 bg-slate-800/50 rounded-md">
                                <span className="font-mono text-xl text-purple-400 w-12 text-center">{s.symbol}</span>
                                <div>
                                    <p className="font-semibold text-slate-200">{s.name}</p>
                                    <p className="text-sm text-slate-400">{s.description}</p>
                                </div>
                            </div>
                        ))}
                    </div>
                )}
                {activeTab === 'domains' && (
                    <div className="space-y-3">
                         {domains.map(d => (
                            <div key={d.name} className="p-3 bg-slate-800/50 rounded-md">
                                <p className="font-semibold text-slate-200">{d.name}</p>
                                <p className="text-sm text-slate-400 mt-1">{d.description}</p>
                            </div>
                        ))}
                    </div>
                )}
            </div>
        </div>
    );
};

export default Explanation;
